-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_mem_ball_a4fbc7617a44
-- name    : P2M_Formalism_BasicNotions_Examples__LB_mem_ball_a4fbc7617a44
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:30.731477+00:00
-- url     : https://prove2.me/theorems/a050439b-1c9b-4524-bc03-62f01558056f
-- title:
--   P2 M Formalism Basic Notions Examples  LB mem ball a4fbc7617a44: P2 M Formalism Basic Notions Examples  LB mem ball a4fbc7617a44
-- statement:
--   The P2 M Formalism Basic Notions Examples  LB mem ball a4fbc7617a44 construction uses the P2 M Formalism Basic Notions Examples  LB mem ball a4fbc7617a44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocA.lean#L50-L55

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]

theorem P2M_Formalism_BasicNotions_Examples__LB_mem_ball_a4fbc7617a44 (x : PadicAlgCl l) : x ∈ ball l ↔ ‖x‖ ≤ 1 := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«LB».«mem_ball» := P2M_Formalism_BasicNotions_Examples__LB_mem_ball_a4fbc7617a44
