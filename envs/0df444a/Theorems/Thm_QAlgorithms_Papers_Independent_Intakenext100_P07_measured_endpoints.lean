-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_measured_endpoints
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.measured_endpoints
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:59:40.404444+00:00
-- url     : https://prove2.me/theorems/542d6a1b-4a65-4d10-b69b-45c06ead60dd
-- title:
--   §4.3.3 (4.84): measured endpoint representation
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   For α=1/2 or ∞, Dtildeα(ρ||σ)=max over single-copy measurements Dα(Mρ||Mσ); hence positivity-preserving trace-preserving maps suffice for DPI at these endpoints.
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma)=\max_{\mathcal M}D_\alpha(\mathcal M(\rho)\|\mathcal M(\sigma)),\qquad\alpha\in\{1/2,\infty\}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 68, §4.3.3 (4.84): measured endpoint representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#4.measuredendpoints
Equation (4.84) and following remarks, PDF p.68. Printed: M(rho) twice.
Changed: M(sigma) in the second argument. Why: the left side and its DPI application require sigma. -/
theorem measured_endpoints [Nonempty I] [Nonempty J] (r s : paperMat I)
    (hr : r.PosSemidef) (hne : r ≠ 0) (hs : s.PosSemidef) (a : ENNReal) (ha : a = 1/2 ∨ a = ⊤) :
    (∃ m : ℕ, 0 < m ∧ ∃ M : Fin m → paperMat I, IsPOVM M ∧
      paperRenyi true r s a = paperRenyi false (measureOutput M r) (measureOutput M s) a ∧
      ∀ k : ℕ, 0 < k → ∀ N : Fin k → paperMat I, IsPOVM N →
        paperRenyi false (measureOutput N r) (measureOutput N s) a ≤ paperRenyi true r s a) ∧
    (∀ E : paperMat I →ₗ[ℂ] paperMat J, (∀ R : paperMat I, R.PosSemidef → (E R).PosSemidef) →
      (∀ R : paperMat I, (E R).trace = R.trace) → paperRenyi true (E r) (E s) a ≤ paperRenyi true r s a) ∧
    (∀ b : ENNReal, 1/2 ≤ b → ∀ E : paperMat I →ₗ[ℂ] paperMat J,
      (∀ n : ℕ, ∀ R : paperMat (Fin n → I), R.PosSemidef → (piSuperop (fun _ : Fin n => E) R).PosSemidef) →
      (∀ R : paperMat I, (E R).trace = R.trace) → paperRenyi true (E r) (E s) b ≤ paperRenyi true r s b) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
