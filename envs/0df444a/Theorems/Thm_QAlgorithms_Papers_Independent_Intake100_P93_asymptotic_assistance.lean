-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_asymptotic_assistance
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.asymptotic_assistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:35:16.326697+00:00
-- url     : https://prove2.me/theorems/4fd12354-9a25-4ba4-a66e-4138075ddf72
-- title:
--   Theorem 1 / abstract: asymptotic entanglement of assistance
-- statement:
--   Let $|\psi\rangle^{ABC}$ be a normalized pure state on three nonzero finite-dimensional local spaces. Each party may act jointly on its own $n$ copies, use local ancillary states, dispose of systems, and exchange classical messages. No shared entanglement or quantum side communication is supplied. Write $S(X)$ for the von Neumann entropy in bits of the actual marginal on $X$. The optimal asymptotic Bell-pair yield between $A$ and $B$ is
--
--   $$E_A^\infty(\psi^{ABC})=\min\{S(A),S(B)\}.$$
--
--   Equivalently, a nonnegative rate $r$ is achievable with joint target fidelity tending to one precisely when $r\le\min\{S(A),S(B)\}$. For every normalized bipartite mixed state $\rho^{AB}$, the same operational yield, with a purification held by $C$, is $\min\{S(\rho^A),S(\rho^B)\}$. This identifies the assisted distillation resource, including pure and product-state inputs.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 2, Theorem 1 / abstract: asymptotic entanglement of assistance

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF pp.1--3, Theorem 1 and abstract: optimal assistance equals the smaller
local entropy, for a pure tripartite source and for a mixed AB source with its
purification held by C. Threshold form includes the optimal rate itself. -/
theorem asymptotic_assistance {d : Fin 3 → ℕ} (hd : ∀ i, 0 < d i)
    (psi : EuclideanSpace ℂ (AssistanceBasis d)) (hpsi : ‖psi‖ = 1) :
    (∀ r : ℝ, AssistedYield (pureDensity psi) .locc 0 1 0 r ↔
      0 ≤ r ∧ r ≤ min (partyEntropy (pureDensity psi) {0}) (partyEntropy (pureDensity psi) {1})) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → ∀ rho : Op (Fin a × Fin b),
      IsDensityMatrix rho → operationalAssistance rho =
        min (vnEntropy (traceRight rho)) (vnEntropy (traceLeft rho))) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
