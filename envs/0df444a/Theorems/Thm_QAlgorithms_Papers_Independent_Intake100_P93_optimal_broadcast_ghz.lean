-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_optimal_broadcast_ghz
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.optimal_broadcast_ghz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:41:18.338531+00:00
-- url     : https://prove2.me/theorems/9ce84eac-4bae-4067-9284-0cd0def55fc8
-- title:
--   Theorem 9: optimal one-way-broadcast GHZ rate
-- statement:
--   Let $\psi^{ABC}$ be a normalized pure state on nonzero finite-dimensional spaces. Restrict protocols to one instrument at $C$, one broadcast of its outcome to $A,B$, and message-dependent local channels at $A$ and $B$, without feedback or communication between the receivers. The optimal asymptotic GHZ rate is
--
--   $$R_{\rm GHZ}^{C\to AB}=\min\{S(A),S(B)\}-E_C(\psi^{AB}).$$
--
--   Here $E_C$ is the operational entanglement cost of the actual $AB$ marginal; entropies and rates are in bits. Nonnegative rates below this value, including the endpoint in rate closure, are exactly achievable with vanishing joint error. The converse is Theorem 9 and achievability is the optimality assertion on p.2 using Theorem 2 on large blocks. This characterizes the restricted protocol class.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 6, Theorem 9: optimal one-way-broadcast GHZ rate

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

/-- PDF pp.2,6, Theorem 9 and its stated optimality conclusion: exact threshold
for this restricted class. Entanglement cost is the accepted operational cost
of the computed AB marginal; it is not single-copy formation. -/
theorem optimal_broadcast_ghz {d : Fin 3 → ℕ} (hd : ∀ i, 0 < d i)
    (psi : EuclideanSpace ℂ (AssistanceBasis d)) (hpsi : ‖psi‖ = 1) :
    ∀ r : ℝ, AssistedYield (pureDensity psi) (.broadcast 2) 0 1 r 0 ↔
      0 ≤ r ∧ r ≤ min (partyEntropy (pureDensity psi) {0}) (partyEntropy (pureDensity psi) {1}) -
        Dependency50.P42.entanglementCost Dependency50.P42.paperBures
          (pairMarginal (pureDensity psi) 0 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
