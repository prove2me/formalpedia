-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemma2_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemma2_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:32:29.487772+00:00
-- url     : https://prove2.me/theorems/71a5a92d-3e39-48c4-be90-6dfb87343256
-- title:
--   Stability under nonexponentially unlikely CP maps
-- statement:
--   Let $\rho$ be a density operator and $\sigma\ge0$ on a nonzero finite-dimensional complex Hilbert space. For each positive integer $n$, let $W_n$ be a completely positive trace non-increasing map on the $n$-fold tensor product. Suppose that for every $\xi>0$, $\liminf_n e^{\xi n}\operatorname{tr}W_n(\rho^{\otimes n})>0$. Then, with normalized base-two relative entropy and extended limits,
--
--   $$\limsup_{n\to\infty}\frac1n D\bigl(W_n(\rho^{\otimes n})\|W_n(\sigma^{\otimes n})\bigr)\le D(\rho\|\sigma).$$
--
--   The trace assumption permits initial zero outputs and guarantees eventual nonzero first arguments. The result controls relative entropy after postselection.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 6, Lemma 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma 2.3 (PDF pp.6–7): extended liminf/limsup; nonzero outputs only eventually. -/
theorem lemma2_3 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : IsDensityMatrix rho) (hsigma : sigma.PosSemidef)
    (W : (n : ℕ) → Superop (Fin (n+1) → I) (Fin (n+1) → I))
    (hW : ∀ n, TNI (W n))
    (htrace : ∀ xi : ℝ, 0 < xi → (0 : EReal) <
      Filter.liminf (fun n => ((Real.exp (xi * ((n+1 : ℕ) : ℝ)) *
        (W n (matrixPower rho (n+1))).trace.re : ℝ) : EReal)) atTop) :
    Filter.limsup (fun n => (((n+1 : ℕ) : ℝ)⁻¹ : EReal) *
      normalizedRelativeEntropyBits (W n (matrixPower rho (n+1))) (W n (matrixPower sigma (n+1)))) atTop ≤
        normalizedRelativeEntropyBits rho sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
