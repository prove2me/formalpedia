-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_almostMixed_chernoff
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.almostMixed_chernoff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:54:12.720333+00:00
-- url     : https://prove2.me/theorems/87c76e76-ed17-4221-8935-057bd8465dda
-- title:
--   Corollary 1: Chernoff estimate for almost-power mixtures
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space of dimension $d\ge1$, with a fixed orthonormal basis. All states below are positive operators of trace one; pure states are unit vectors. Write $\|\cdot\|_1$ for the full trace norm (the full $\ell_1$ norm for classical distributions), $H_2$ for binary entropy in bits, and define
--   $$
--   e(\delta,N,r,w)=2^{-N[\delta^2/4-H_2(r/N)]+w\log_2(N/2+1)}.
--   $$
--
--   Let $n\ge1$, $2r\le n$, $\delta>0$, and let $\theta$ be a unit vector. Let $\rho_n$ be a convex mixture of projectors onto unit vectors in $\operatorname{Sym}(\mathcal H^{\otimes n})$ intersected with the complex span of permutations of $\theta^{\otimes(n-r)}\otimes\psi_r$. For every finite normalized POVM $M=\{M_a\}_{a=1}^w$, set $P_a=\operatorname{Tr}(M_a|\theta\rangle\langle\theta|)$ and let $Q$ be the normalized empirical frequencies under the product measurement on $\rho_n$. Then
--   $$
--   \Pr_{\rho_n}\{\|P-Q\|_1>\delta\}\le e(\delta,n,r,w).
--   $$
--
--   This extends the fixed deviation event bound to convex mixtures.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 14, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.14, Corollary 1: the fixed deviation event probability extends
linearly to mixtures; empirical frequencies themselves are not linear in rho. -/
theorem almostMixed_chernoff {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (theta : Vec I) (htheta : IsState theta) (n r w : ℕ)
    (hn : 0 < n) (hr : 2 * r ≤ n) (hw : 0 < w)
    (rho : Op (Copies I n)) (halmost : AlmostMixed theta n r rho)
    (E : Fin w → Op I) (hE : IsPOVM E) (delta : ℝ) (hdelta : 0 < delta) :
    iidEvent rho E (fun out =>
      l1 (fun a => effectProb (E a) (pureDensity theta)) (empiricalFrequency out) > delta) ≤
        chernoffError delta n r w := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
