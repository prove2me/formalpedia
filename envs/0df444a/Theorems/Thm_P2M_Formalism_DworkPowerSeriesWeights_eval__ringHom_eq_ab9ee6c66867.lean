-- Prove2me | Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867
-- name    : P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:16.943372+00:00
-- url     : https://prove2.me/theorems/bf7917df-2a0b-41b4-acf5-886bab356aa5
-- title:
--   P2 M Formalism Dwork Power Series Weights eval  ring Hom eq ab9ee6c66867: P2 M Formalism Dwork Power Series Weights eval  ring Hom eq ab9ee6c66867
-- statement:
--   The P2 M Formalism Dwork Power Series Weights eval  ring Hom eq ab9ee6c66867 construction uses the P2 M Formalism Dwork Power Series Weights eval  ring Hom eq ab9ee6c66867 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L217-L221

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867 {σ A K : Type} [CommRing A] [CommRing K] (ι : MvPolynomial σ A →+* K)
    (P : MvPolynomial σ A) : eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := by sorry

alias «Formalism».«DworkPowerSeriesWeights».«eval₂_ringHom_eq» := P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867
