-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_conditional_local_properties
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.conditional_local_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:47:58.489987+00:00
-- url     : https://prove2.me/theorems/519128b1-8879-466c-ba61-19ec48c7a44f
-- title:
--   §5.2.3: local isometries, sub-unital maps, and curvature
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion. The upward conditional entropy optimizes the negative divergence over normalized reference states on the conditioning system; the downward entropy uses the actual marginal. The notation $H(A|B)=H(AB)-H(B)$ denotes conditional von Neumann entropy.
--
--   All four entropies in their DPI ranges are invariant under arbitrary local isometries; sub-unital CPTP operations on A cannot decrease entropy; TNI maps preserving this input trace have the analogous properties. Petz entropies concave for 0≤α≤1 and quasi-concave for 1≤α≤2; sandwiched concave for 1/2≤α≤1, quasi-concave for α>1.
--
--   $$
--   H_\alpha(A^\prime|B^\prime)_{(U\otimes V)\rho(U\otimes V)^\dagger}=H_\alpha(A|B)_\rho;\qquad H_\alpha\text{ has the stated concavity and quasi-concavity ranges}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 81, §5.2.3: local isometries, sub-unital maps, and curvature

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

/-- NODE paper:1504.00233#5.localproperties
§5.2.3: local isometries, sub-unital maps, and curvature, arXiv:1504.00233v5, PDF p.81. -/
theorem conditional_local_properties [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (r : paperMat (A × B)) (hr : IsDensityMatrix r) (sand up : Bool) (a : ENNReal) :
    (∀ U : Matrix C A ℂ, ∀ V : Matrix D B ℂ, Uᴴ*U = 1 → Vᴴ*V = 1 →
      paperConditional sand up a (paperLocalEmbedding U V r) = paperConditional sand up a r) ∧
    (DPIOrder sand a → ∀ E : paperMat A →ₗ[ℂ] paperMat C, ∀ F : paperMat B →ₗ[ℂ] paperMat D,
      CPTNI E → CPTNI F → paperBelow (E 1) 1 → (paperTensorAction E F r).trace = r.trace →
      paperConditional sand up a r ≤ paperConditional sand up a (paperTensorAction E F r)) ∧
    (DPIOrder sand a → ∀ s : paperMat (A × B), IsDensityMatrix s → ∀ l : ℝ, l ∈ Set.Icc 0 1 →
      (a ≤ 1 → (l:EReal)*paperConditional sand up a r+((1-l:ℝ):EReal)*paperConditional sand up a s ≤ paperConditional sand up a (paperMix l r s)) ∧
      (1 ≤ a → min (paperConditional sand up a r) (paperConditional sand up a s) ≤ paperConditional sand up a (paperMix l r s))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
