-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_EmbeddingTypeJumps_crd_low
-- name    : UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:37.812191+00:00
-- url     : https://prove2.me/theorems/eddcbc69-33eb-4be5-bde5-e5d10eb7c829
-- title:
--   Embedding Type Jumps: crd low
-- statement:
--   The Embedding Type Jumps construction uses the crd low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EmbeddingTypeJumps.lean#L49-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EmbeddingTypeJumps.lean#L49-L70

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EmbeddingTypeJumps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd_low :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E]
      [inst_5 : StarRing E] (W : Formalism.BasicNotions.HSpace E),
      ∃ (c : NumberField.RingOfIntegers F),
        c ≠ (0 : NumberField.RingOfIntegers F) ∧
          ∀ (i : Fin W.rank) (e : E), IsIntegral ℤ e → Pi.single i ((↑c : F) • e) ∈ UpperTheory.Reformulated.B.EmbeddingTypeJumps.crd W := by sorry
