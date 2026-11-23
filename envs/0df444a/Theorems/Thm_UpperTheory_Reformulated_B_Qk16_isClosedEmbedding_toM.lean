-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk16_isClosedEmbedding_toM
-- name    : UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:31.262557+00:00
-- url     : https://prove2.me/theorems/a31ba0ed-cd04-47ae-b3ab-1742c97b8393
-- title:
--   Qk16: is Closed Embedding to M
-- statement:
--   The Qk16 construction uses the is Closed Embedding to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsClosedEmbeddingToM.lean#L80-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsClosedEmbeddingToM.lean#L80-L117

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM :
    ∀ {n : ℕ} (ε : Fin n → Bool), Topology.IsClosedEmbedding fun (g : ↥(UpperTheory.Reformulated.B.Qk16.UJ ε)) ↦ UpperTheory.Reformulated.B.Qk16.toM g := by sorry
