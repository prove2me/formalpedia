-- Prove2me | Theorems.Thm_P2M_PI_OneCosetSharp_W_C2_toLin__eN_a4eb870cf892
-- name    : P2M_PI_OneCosetSharp_W_C2_toLin__eN_a4eb870cf892
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:14.800913+00:00
-- url     : https://prove2.me/theorems/dd722e02-20a6-4c47-8652-9c6bb8b29360
-- title:
--   P2 M PI One Coset Sharp W C2 to Lin  e N a4eb870cf892: P2 M PI One Coset Sharp W C2 to Lin  e N a4eb870cf892
-- statement:
--   The P2 M PI One Coset Sharp W C2 to Lin  e N a4eb870cf892 construction uses the P2 M PI One Coset Sharp W C2 to Lin  e N a4eb870cf892 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L11-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]

theorem P2M_PI_OneCosetSharp_W_C2_toLin__eN_a4eb870cf892 {A B : ℕ} (X : Matrix (Fin B) (Fin A) k) (i : ℕ) (hi : i < A) :
    Matrix.toLin' X (eN k A i) = fun l => X l ⟨i, hi⟩ := by sorry

alias «PI».«OneCosetSharp».«W».«C2».«toLin'_eN» := P2M_PI_OneCosetSharp_W_C2_toLin__eN_a4eb870cf892
