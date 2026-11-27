-- Prove2me | Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow__b134f1ece94e
-- name    : P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow__b134f1ece94e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:17:26.852272+00:00
-- url     : https://prove2.me/theorems/a3fb3d28-19d9-4a48-87d1-83b57d894f76
-- title:
--   P2 M Formalism L2 Formal Series Bounds Gm Ex Arith ge pow  b134f1ece94e: P2 M Formalism L2 Formal Series Bounds Gm Ex Arith ge pow  b134f1ece94e
-- statement:
--   The P2 M Formalism L2 Formal Series Bounds Gm Ex Arith ge pow  b134f1ece94e construction uses the P2 M Formalism L2 Formal Series Bounds Gm Ex Arith ge pow  b134f1ece94e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L63-L70

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}

theorem P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow__b134f1ece94e {r : ℝ} {a : C} (h : V.Ge r a) (k : ℕ) : V.Ge ((k : ℝ) * r) (a ^ k) := by sorry

alias «Formalism».«L2».«FormalSeriesBounds».«GmExArith».«ge_pow'» := P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow__b134f1ece94e
