-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_coefficient_from_casimirs
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.coefficient_from_casimirs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:45:00.721014+00:00
-- url     : https://prove2.me/theorems/dc05245b-7fa9-4fd2-b021-cc6766c4a4e5
-- title:
--   Casimir formula for an irreducible block coefficient
-- statement:
--   Let $d\ge2$ and $N\ge1$, and put $K=\operatorname{Sym}^N\mathbb C^d$ with its actual tensor representation $\pi_N^+$. Let $\pi_m$ and $\pi_n$ be actual irreducible smooth finite-dimensional unitary $U(d)$ representations with dominant integral highest weights $m,n\in\mathbb Z^d$. Let $V:K\to H_m\otimes H_n$ be any isometric intertwiner. Define
--   $$
--   c(m)=\sum_jm_j^2+\sum_{j<k}(m_j-m_k)-\frac1d\left(\sum_jm_j\right)^2,\qquad s=(N,0,\ldots,0).
--   $$
--   Then $c(s)>0$, and for every traceless complex matrix $X$,
--   $$
--   V^*(\partial\pi_m(X)\otimes I)V=\left(\frac12+\frac{c(m)-c(n)}{2c(s)}\right)\partial\pi_N^+(X).
--   $$
--   All differentials are the actual infinitesimal actions, complexified to arbitrary traceless matrices. In particular the coefficient depends only on the irreducible labels, independently of $V$. The positive Appendix A8 convention is used uniformly; in dimension two the common Casimir scale cancels and gives Eq.(18).
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 8, §III D–E, Eqs.(17),(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF pp.7–8 Eqs.(17),(21): Casimir labels fix the coefficient independently
of the chosen isometric intertwiner. Uniform positive A8 normalization avoids
the inconsistent anti-Hermitian sum-of-squares sign on p.7. -/
theorem coefficient_from_casimirs (d N a b : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (pa : SmoothUnitaryRep d a) (pb : SmoothUnitaryRep d b)
    (m n : Fin d → ℤ) (hm : HasHighestWeight pa m) (hn : HasHighestWeight pb n)
    (V : Matrix (Fin a × Fin b) (Word N d) ℂ) (hV : IsTensorIntertwiner pa pb V) :
    0 < casimirValue (symmetricWeight d N) ∧
    ∀ X : Mat d, Matrix.trace X = 0 →
      Vᴴ * Matrix.kronecker (pa.differential X) (1 : Mat b) * V =
        (weightCoefficient N m n : ℂ) • boseGenerator d N X := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
