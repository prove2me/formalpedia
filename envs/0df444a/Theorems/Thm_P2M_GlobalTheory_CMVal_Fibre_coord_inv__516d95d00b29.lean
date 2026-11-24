-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CMVal_Fibre_coord_inv__516d95d00b29
-- name    : P2M_GlobalTheory_CMVal_Fibre_coord_inv__516d95d00b29
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:06.276791+00:00
-- url     : https://prove2.me/theorems/cffe3b7d-3f47-46b9-8959-4d9b8f8fd0a5
-- title:
--   P2 M Global Theory CMVal Fibre coord inv  516d95d00b29: P2 M Global Theory CMVal Fibre coord inv  516d95d00b29
-- statement:
--   The P2 M Global Theory CMVal Fibre coord inv  516d95d00b29 construction uses the P2 M Global Theory CMVal Fibre coord inv  516d95d00b29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L57-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]

theorem P2M_GlobalTheory_CMVal_Fibre_coord_inv__516d95d00b29 (P : HeightOneSpectrum (𝓞 E)) (y : (Af E)ˣ) : coord P y⁻¹ = (coord P y)⁻¹ := by sorry

alias «GlobalTheory».«CMVal».«Fibre».«coord_inv'» := P2M_GlobalTheory_CMVal_Fibre_coord_inv__516d95d00b29
