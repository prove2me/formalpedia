-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_subst_neg__662fad9e4892
-- name    : P2M_Formalism_L2_Th1_A_subst_neg__662fad9e4892
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:01.515802+00:00
-- url     : https://prove2.me/theorems/7d54a05a-63c3-4d73-aa6d-75af82c7523f
-- title:
--   P2 M Formalism L2 Th1 A subst neg  662fad9e4892: P2 M Formalism L2 Th1 A subst neg  662fad9e4892
-- statement:
--   The P2 M Formalism L2 Th1 A subst neg  662fad9e4892 construction uses the P2 M Formalism L2 Th1 A subst neg  662fad9e4892 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/LogExp.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/LogExp.lean#L16-L19

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

theorem P2M_Formalism_L2_Th1_A_subst_neg__662fad9e4892 {a : R⟦X⟧} (ha : HasSubst a) (f : R⟦X⟧) : (-f).subst a = -f.subst a := by sorry

alias «Formalism».«L2».«Th1».«A».«subst_neg'» := P2M_Formalism_L2_Th1_A_subst_neg__662fad9e4892
