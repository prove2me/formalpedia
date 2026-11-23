-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913
-- name    : P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:46.696898+00:00
-- url     : https://prove2.me/theorems/5c1183c2-236f-49c8-a7e8-e293063afaa1
-- title:
--   P2 M Global Theory Tw Centralizer Adjoin adj one  bd9885609913: P2 M Global Theory Tw Centralizer Adjoin adj one  bd9885609913
-- statement:
--   The P2 M Global Theory Tw Centralizer Adjoin adj one  bd9885609913 construction uses the P2 M Global Theory Tw Centralizer Adjoin adj one  bd9885609913 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L132-L135

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

theorem P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913 {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ 1 = 1 := by sorry

alias «GlobalTheory».«Tw».«CentralizerAdjoin».«adj_one'» := P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_one__bd9885609913
