-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_vonNeumann_structure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.vonNeumann_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:46:38.493194+00:00
-- url     : https://prove2.me/theorems/6d7e13c1-76b5-4cb0-8388-7ce8341ed8cf
-- title:
--   §5.1 (5.6)–(5.15): von Neumann entropy structure
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   For normalized states: SSA, full side-information CPTP DPI, |H(A)−H(B)|≤H(AB)≤H(A)+H(B), and H(A|B)=−D(ρ_AB||I_A⊗ρ_B)=max_{density σ_B}−D(ρ_AB||I_A⊗σ_B), with optimizer ρ_B.
--
--   $$
--   H(ABC)+H(B)\le H(AB)+H(BC),\qquad H(A|B)=-D(\rho_{AB}\|I_A\otimes\rho_B)=\max_{\sigma_B\in\mathcal S_\circ}-D(\rho_{AB}\|I_A\otimes\sigma_B).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 76, §5.1 (5.6)–(5.15): von Neumann entropy structure

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

/-- NODE paper:1504.00233#5.vn
§5.1 (5.6)–(5.15): von Neumann entropy structure, arXiv:1504.00233v5, PDF p.76. -/
theorem vonNeumann_structure [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] :
    (∀ r : paperMat ((A × B) × C), IsDensityMatrix r →
      vnEntropy r+vnEntropy (traceRight (paperMarginalBC r)) ≤ vnEntropy (traceRight r)+vnEntropy (paperMarginalBC r) ∧
      conditionalVN (paperRegroup r) ≤ conditionalVN (traceRight r)) ∧
    (∀ r : paperMat (A × B), IsDensityMatrix r → ∀ E : paperMat B →ₗ[ℂ] paperMat D, paperCPTP E →
      conditionalVN r ≤ conditionalVN (idTensorSuperop E r)) ∧
    (∀ r : paperMat (A × B), IsDensityMatrix r →
      |vnEntropy (traceRight r)-vnEntropy (traceLeft r)| ≤ vnEntropy r ∧
      vnEntropy r ≤ vnEntropy (traceRight r)+vnEntropy (traceLeft r) ∧
      (conditionalVN r:EReal) = -paperRelativeD r (Matrix.kronecker (1:paperMat A) (traceLeft r)) ∧
      (∃ s : paperMat B, IsDensityMatrix s ∧ (conditionalVN r:EReal) = -paperRelativeD r (Matrix.kronecker (1:paperMat A) s)) ∧
      (∀ s : paperMat B, IsDensityMatrix s → -paperRelativeD r (Matrix.kronecker (1:paperMat A) s) ≤ (conditionalVN r:EReal))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
