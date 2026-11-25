-- Prove2me | Theorems.Thm_UpperTheory_congruence_subgroup_eventually
-- name    : UpperTheory.congruence_subgroup_eventually
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:08:01.099484+00:00
-- url     : https://prove2.me/theorems/b8ee3b8e-3c98-4932-8607-885d47fe622e
-- title:
--   Upper Theory: congruence subgroup eventually
-- statement:
--   The Upper Theory construction uses the congruence subgroup eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CongruenceSubgroupEventually.lean#L66-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CongruenceSubgroupEventually.lean#L66-L88

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CongruenceSubgroupEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ValuativeRel

theorem UpperTheory.congruence_subgroup_eventually :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) →
        ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∀ g : GL (Fin n) k, g ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker → g ∈ U := by sorry
