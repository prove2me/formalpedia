-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_isUnit_theta__778c4ab65804
-- name    : P2M_GlobalTheory_Tw_CentralizerAdjoin_isUnit_theta__778c4ab65804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:58.964791+00:00
-- url     : https://prove2.me/theorems/6951b8bb-71bd-41e5-8a76-083492a232df
-- title:
--   P2 M Global Theory Tw Centralizer Adjoin is Unit theta  778c4ab65804: P2 M Global Theory Tw Centralizer Adjoin is Unit theta  778c4ab65804
-- statement:
--   The P2 M Global Theory Tw Centralizer Adjoin is Unit theta  778c4ab65804 construction uses the P2 M Global Theory Tw Centralizer Adjoin is Unit theta  778c4ab65804 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L145-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Tw Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.CentralizerAdjoin
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model

theorem P2M_GlobalTheory_Tw_CentralizerAdjoin_isUnit_theta__778c4ab65804 {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : IsUnit (theta δ) := by sorry

alias «GlobalTheory».«Tw».«CentralizerAdjoin».«isUnit_theta'» := P2M_GlobalTheory_Tw_CentralizerAdjoin_isUnit_theta__778c4ab65804
