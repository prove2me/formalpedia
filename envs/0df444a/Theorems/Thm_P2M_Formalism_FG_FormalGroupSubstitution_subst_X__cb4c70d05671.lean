-- Prove2me | Theorems.Thm_P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671
-- name    : P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:42.237119+00:00
-- url     : https://prove2.me/theorems/2eb9478c-3e1a-49bd-b133-cb554c2435cb
-- title:
--   P2 M Formalism FG Formal Group Substitution subst X  cb4c70d05671: P2 M Formalism FG Formal Group Substitution subst X  cb4c70d05671
-- statement:
--   The P2 M Formalism FG Formal Group Substitution subst X  cb4c70d05671 construction uses the P2 M Formalism FG Formal Group Substitution subst X  cb4c70d05671 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L15-L18

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupSubstitution
open MvPowerSeries

theorem P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671 {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p : σ) :
    subst a (X p : MvPowerSeries σ R) = a p := by sorry

alias «Formalism».«FG».«FormalGroupSubstitution».«subst_X'» := P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671
