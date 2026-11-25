-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__of_mulVec_eq_ac3453965221
-- name    : P2M_Formalism_BasicNotions_Examples__of_mulVec_eq_ac3453965221
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:12.556012+00:00
-- url     : https://prove2.me/theorems/fbf54586-14e2-4cf8-b86f-c1aed87447fc
-- title:
--   P2 M Formalism Basic Notions Examples  of mul Vec eq ac3453965221: P2 M Formalism Basic Notions Examples  of mul Vec eq ac3453965221
-- statement:
--   The P2 M Formalism Basic Notions Examples  of mul Vec eq ac3453965221 construction uses the P2 M Formalism Basic Notions Examples  of mul Vec eq ac3453965221 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}

theorem P2M_Formalism_BasicNotions_Examples__of_mulVec_eq_ac3453965221 (γ : Matrix (Fin N) (Fin N) E) (v : Fin N → Fin N → E) :
    Matrix.of (fun j => γ.mulVec (v j)) = Matrix.of v * γ.transpose := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«of_mulVec_eq» := P2M_Formalism_BasicNotions_Examples__of_mulVec_eq_ac3453965221
