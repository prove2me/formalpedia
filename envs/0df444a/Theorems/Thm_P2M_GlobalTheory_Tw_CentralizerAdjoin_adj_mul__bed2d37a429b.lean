-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b
-- name    : P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:33.455938+00:00
-- url     : https://prove2.me/theorems/80afe580-a80f-425b-9ffa-8f6cc0e67d62
-- title:
--   P2 M Global Theory Tw Centralizer Adjoin adj mul  bed2d37a429b: P2 M Global Theory Tw Centralizer Adjoin adj mul  bed2d37a429b
-- statement:
--   The P2 M Global Theory Tw Centralizer Adjoin adj mul  bed2d37a429b construction uses the P2 M Global Theory Tw Centralizer Adjoin adj mul  bed2d37a429b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedCentralizerIsNormOneTorus.lean#L120-L125

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

theorem P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (g * h) = adj δ h * adj δ g := by sorry

alias «GlobalTheory».«Tw».«CentralizerAdjoin».«adj_mul'» := P2M_GlobalTheory_Tw_CentralizerAdjoin_adj_mul__bed2d37a429b
