-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc
-- name    : P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:58.347446+00:00
-- url     : https://prove2.me/theorems/e2b24cbe-55c5-433d-b34d-9850199165db
-- title:
--   P2 M Global Theory Sg Glob Inhab mem one iff  00678d2868dc: P2 M Global Theory Sg Glob Inhab mem one iff  00678d2868dc
-- statement:
--   The P2 M Global Theory Sg Glob Inhab mem one iff  00678d2868dc construction uses the P2 M Global Theory Sg Glob Inhab mem one iff  00678d2868dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L178-L180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]

theorem P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc (x : E) : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ x ∈ Int' E := by sorry

alias «GlobalTheory».«SgGlob».«Inhab».«mem_one_iff'» := P2M_GlobalTheory_SgGlob_Inhab_mem_one_iff__00678d2868dc
