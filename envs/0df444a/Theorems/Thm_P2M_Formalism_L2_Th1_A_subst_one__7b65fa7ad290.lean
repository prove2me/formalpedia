-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_subst_one__7b65fa7ad290
-- name    : P2M_Formalism_L2_Th1_A_subst_one__7b65fa7ad290
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:42.87014+00:00
-- url     : https://prove2.me/theorems/6868e067-f2e8-47a7-85e4-87cc4b0de933
-- title:
--   P2 M Formalism L2 Th1 A subst one  7b65fa7ad290: P2 M Formalism L2 Th1 A subst one  7b65fa7ad290
-- statement:
--   The P2 M Formalism L2 Th1 A subst one  7b65fa7ad290 construction uses the P2 M Formalism L2 Th1 A subst one  7b65fa7ad290 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/LogExp.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/LogExp.lean#L21-L24

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]

theorem P2M_Formalism_L2_Th1_A_subst_one__7b65fa7ad290 {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by sorry

alias «Formalism».«L2».«Th1».«A».«subst_one'» := P2M_Formalism_L2_Th1_A_subst_one__7b65fa7ad290
