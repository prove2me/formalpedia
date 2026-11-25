-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Th1_A_More_map_subst__08a15fd92527
-- name    : P2M_Formalism_L2_Th1_A_More_map_subst__08a15fd92527
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:12.349296+00:00
-- url     : https://prove2.me/theorems/38b6e3cc-1386-52cd-a090-8497184a9116
-- title:
--   P2 M Formalism L2 Th1 A More map subst  08a15fd92527: P2 M Formalism L2 Th1 A More map subst  08a15fd92527
-- statement:
--   The P2 M Formalism L2 Th1 A More map subst  08a15fd92527 construction uses the P2 M Formalism L2 Th1 A More map subst  08a15fd92527 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L23-L29

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.More
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem P2M_Formalism_L2_Th1_A_More_map_subst__08a15fd92527 (φ : R →+* S) {s : R⟦X⟧} (hs : HasSubst s) (f : R⟦X⟧) :
    PowerSeries.map φ (f.subst s) = (PowerSeries.map φ f).subst (PowerSeries.map φ s) := by sorry

alias «Formalism».«L2».«Th1».«A».«More».«map_subst'» := P2M_Formalism_L2_Th1_A_More_map_subst__08a15fd92527
