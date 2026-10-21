-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P48_pure_state_extrema
-- name    : QAlgorithms.Papers.Independent.Claimed50.P48.pure_state_extrema
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:39:26.561534+00:00
-- url     : https://prove2.me/theorems/ec25f0fe-1e6f-4684-9303-ec96ad8cf13c
-- title:
--   Optimization over pure inputs suffices
-- statement:
--   Let $\Phi$ be a finite-dimensional CP map with nonzero input space, and let $1\le p\le\infty$. There is a unit input vector $\psi$ such that
--
--   $$\|\Phi(|\psi\rangle\langle\psi|)\|_p=\nu_p(\Phi),\qquad
--   \|\Phi(\rho)\|_p\le\|\Phi(|\psi\rangle\langle\psi|)\|_p\quad(\rho\text{ a density}).$$
--
--   If $\Phi$ is a channel, there is also a pure input attaining $\check H(\Phi)$ and minimizing output entropy among all input densities. For every prescribed density $\rho$, a finite pure ensemble $(q_j,\psi_j)$ with $q_j\ge0$, $\sum_jq_j=1$, unit $\psi_j$, and $\sum_jq_j|\psi_j\rangle\langle\psi_j|=\rho$ attains
--
--   $$\widehat H_\Phi(\rho)=\sum_jq_j H(\Phi(|\psi_j\rangle\langle\psi_j|)).$$
--
--   Thus extrema are actual maxima and minima, while the convex roof keeps its mixed barycenter.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, PDF p. 2, Optimization over pure inputs suffices

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF p.2: attained pure-input extrema. The convex roof retains its
prescribed mixed barycenter and attains its minimum over decompositions. -/
theorem pure_state_extrema [Nonempty A] (Phi : Superop A B) (hPhi : FiniteKrausCP Phi)
    (p : ℝ≥0∞) (hp : ValidExponent p) :
    (∃ psi : EuclideanSpace ℂ A, IsState psi ∧ schattenNorm p (Phi (pureDensity psi)) = nu p Phi ∧
      ∀ rho, IsDensityMatrix rho → schattenNorm p (Phi rho) ≤ schattenNorm p (Phi (pureDensity psi))) ∧
    (IsChannel Phi →
      (∃ psi : EuclideanSpace ℂ A, IsState psi ∧ entropy (Phi (pureDensity psi)) = hmin Phi ∧
        ∀ rho, IsDensityMatrix rho → entropy (Phi (pureDensity psi)) ≤ entropy (Phi rho)) ∧
      (∀ rho, IsDensityMatrix rho → ∃ e : PureEnsemble A,
        ensembleDensity e.weight e.vector = rho ∧
        hhat Phi rho = ∑ k, e.weight k * entropy (Phi (pureDensity (e.vector k))))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P48

end
