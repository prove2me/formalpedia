-- Prove2me | Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211
-- name    : P2M_Formalism_G_LogP_subst_zero__b4a287294211
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:04:19.349922+00:00
-- url     : https://prove2.me/theorems/191f342f-2a94-433e-ac99-edb68ccc8085
-- title:
--   P2 M Formalism G Log P subst zero  b4a287294211: P2 M Formalism G Log P subst zero  b4a287294211
-- statement:
--   The P2 M Formalism G Log P subst zero  b4a287294211 construction uses the P2 M Formalism G Log P subst zero  b4a287294211 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L140-L142

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]

theorem P2M_Formalism_G_LogP_subst_zero__b4a287294211 {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by sorry

alias «Formalism».«G».«LogP».«subst_zero'» := P2M_Formalism_G_LogP_subst_zero__b4a287294211
