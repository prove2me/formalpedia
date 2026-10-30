-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_almostMixed_partialTrace
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.almostMixed_partialTrace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:53:31.459646+00:00
-- url     : https://prove2.me/theorems/6cf7ab13-34c7-4929-be10-129a95e2f624
-- title:
--   Lemma 1: stability of almost-power mixtures under partial trace
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space with dimension at least one, and let $\theta$ be a unit vector. For $0\le r\le N$, define the pure almost-power states along $\theta$ to be unit vectors in the intersection of the symmetric subspace of $\mathcal H^{\otimes N}$ and the complex span of all permutations of $\theta^{\otimes(N-r)}\otimes\psi_r$. Write $\operatorname{AP}_{N,r}(\theta)$ for convex mixtures of their rank-one projectors.
--
--   For integers $m\le n$ and $r\le n-m$, every $\rho_n\in\operatorname{AP}_{n,r}(\theta)$ satisfies, for every choice of $m$ discarded sites,
--   $$
--   \operatorname{Tr}_m\rho_n\in\operatorname{AP}_{n-m,r}(\theta).
--   $$
--
--   This is the reduction property used to retain the same defect count when estimating only a subsample. The zero-copy case $n=m=r=0$ is included; no saturated extension to $r>n-m$ is asserted.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 13, Lemma 1

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

/-- PDF pp.12--13, Lemma 1: any discarded m sites, encoded by first permuting
then retaining n-m; r ≤ n-m is the source definition's domain. -/
theorem almostMixed_partialTrace {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (theta : Vec I) (htheta : IsState theta) (n m r : ℕ)
    (hm : m ≤ n) (hr : r ≤ n - m) (rho : Op (Copies I n))
    (halmost : AlmostMixed theta n r rho) :
    ∀ pi : Equiv.Perm (Fin n),
      AlmostMixed theta (n - m) r (reduceCopies (permute pi rho) (n - m) (Nat.sub_le n m)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
