-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_three_way_common_randomness
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.three_way_common_randomness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:41:56.505485+00:00
-- url     : https://prove2.me/theorems/d933edc8-087f-4f9a-8d40-abb5b075f293
-- title:
--   §V proof of Theorem 9: a stronger common-randomness converse
-- statement:
--   For a normalized pure finite-dimensional source $\psi^{ABC}$, consider one-way-broadcast protocols from $C$ to $A,B$. Their output consists of three private $k$-bit strings and the complete public message $X$. Require the joint output law to approach in total variation the law of three identical uniform strings independent of $X$. Every nonnegative achievable i.i.d. rate $r$ satisfies
--
--   $$r\le\min\{S(A),S(B)\}-E_C(\psi^{AB}).$$
--
--   The actual density marginal determines the operational entanglement cost. All public outcomes are retained, and $A,B$ cannot communicate or send feedback. This gives the stronger classical-randomness converse asserted in the proof of Theorem 9; merely broadcasting fresh random bits cannot satisfy its independence requirement.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 6, §V proof of Theorem 9: a stronger common-randomness converse

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

/-- PDF p.6, proof of Theorem 9: the stronger common-randomness converse,
with independence from every public outcome. This is a bound for C-to-AB
one-way broadcast, not unrestricted LOCC. -/
theorem three_way_common_randomness {d : Fin 3 → ℕ} (hd : ∀ i, 0 < d i)
    (psi : EuclideanSpace ℂ (AssistanceBasis d)) (hpsi : ‖psi‖ = 1) :
    ∀ r : ℝ, RandomnessRate (pureDensity psi) r →
      r ≤ min (partyEntropy (pureDensity psi) {0}) (partyEntropy (pureDensity psi) {1}) -
        Dependency50.P42.entanglementCost Dependency50.P42.paperBures
          (pairMarginal (pureDensity psi) 0 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
