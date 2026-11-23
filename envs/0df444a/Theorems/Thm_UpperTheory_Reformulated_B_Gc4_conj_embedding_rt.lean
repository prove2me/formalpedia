-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Gc4_conj_embedding_rt
-- name    : UpperTheory.Reformulated.B.Gc4.conj_embedding_rt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:30.506453+00:00
-- url     : https://prove2.me/theorems/3a17801b-e066-4fcd-8ac8-3cdc067183b3
-- title:
--   Gc4: conj embedding rt
-- statement:
--   The Gc4 construction uses the conj embedding rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjEmbeddingRt.lean#L4-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConjEmbeddingRt.lean#L4-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConjEmbeddingRt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Gc4.conj_embedding_rt :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ),
    (starRingEnd ℂ : ℂ → ℂ) ((τ : E → ℂ) (↑H.rt : E)) =
      -(τ : E → ℂ)
          (↑H.rt :
            E) := by sorry
