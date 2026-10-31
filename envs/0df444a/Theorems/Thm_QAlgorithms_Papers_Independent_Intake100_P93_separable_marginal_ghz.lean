-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_separable_marginal_ghz
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.separable_marginal_ghz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:42:55.42227+00:00
-- url     : https://prove2.me/theorems/48aa8d51-fdb7-47ee-993a-f5f43cb3145b
-- title:
--   §V remark: optimal GHZ distillation when a marginal is separable
-- statement:
--   Let $\psi^{ABC}$ be a normalized pure state on three nonzero finite-dimensional spaces. Every asymptotic GHZ rate obtainable by unrestricted LOCC satisfies
--
--   $$R_{\rm GHZ}\le\min\{S(A),S(B),S(C)\}.$$
--
--   If at least one of $\psi^{AB}$, $\psi^{BC}$ or $\psi^{AC}$ is separable, equality is achievable with vanishing joint error. All local ancillas and disposal are allowed, without quantum messages or initially supplied shared entanglement. This identifies a class for which the unrestricted optimum is determined by local entropies.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 6, §V remark: optimal GHZ distillation when a marginal is separable

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

/-- PDF p.6, remark: unrestricted-LOCC upper bound for every pure source,
and its attainment if ANY one of the three two-party marginals is separable.
SeparablePositive is equivalent to separable density on these trace-one inputs. -/
theorem separable_marginal_ghz {d : Fin 3 → ℕ} (hd : ∀ i, 0 < d i)
    (psi : EuclideanSpace ℂ (AssistanceBasis d)) (hpsi : ‖psi‖ = 1) :
    (∀ r : ℝ, AssistedYield (pureDensity psi) .locc 0 1 r 0 →
      r ≤ min (min (partyEntropy (pureDensity psi) {0}) (partyEntropy (pureDensity psi) {1}))
        (partyEntropy (pureDensity psi) {2})) ∧
    ((Entanglement.IsSeparablePositive (pairMarginal (pureDensity psi) 0 1) ∨
      Entanglement.IsSeparablePositive (pairMarginal (pureDensity psi) 1 2) ∨
      Entanglement.IsSeparablePositive (pairMarginal (pureDensity psi) 0 2)) →
      AssistedYield (pureDensity psi) .locc 0 1
        (min (min (partyEntropy (pureDensity psi) {0}) (partyEntropy (pureDensity psi) {1}))
          (partyEntropy (pureDensity psi) {2})) 0) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
