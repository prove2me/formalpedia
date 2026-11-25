-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_HermInv_conj_pow__9062d8b5e658
-- name    : P2M_GlobalTheory_JR_HermInv_conj_pow__9062d8b5e658
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:51.063268+00:00
-- url     : https://prove2.me/theorems/40db9760-b1fb-4475-a8de-b41d320bfdf5
-- title:
--   P2 M Global Theory JR Herm Inv conj pow  9062d8b5e658: P2 M Global Theory JR Herm Inv conj pow  9062d8b5e658
-- statement:
--   The P2 M Global Theory JR Herm Inv conj pow  9062d8b5e658 construction uses the P2 M Global Theory JR Herm Inv conj pow  9062d8b5e658 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L406-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L406-L413

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}

theorem P2M_GlobalTheory_JR_HermInv_conj_pow__9062d8b5e658 (h h' M : Matrix (Fin r) (Fin r) E) (hh : h' * h = 1) (hh' : h * h' = 1) (k : ℕ) :
    (h * M * h') ^ k = h * M ^ k * h' := by sorry

alias «GlobalTheory».«JR».«HermInv».«conj_pow'» := P2M_GlobalTheory_JR_HermInv_conj_pow__9062d8b5e658
