-- Prove2me | Theorems.Thm_P2M_ChromaticReconstruction_floor_half_le_tau__f5e5110d9215
-- name    : P2M_ChromaticReconstruction_floor_half_le_tau__f5e5110d9215
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:14:20.991499+00:00
-- url     : https://prove2.me/theorems/8b53c676-c23e-440b-8b49-483e3f9f677b
-- title:
--   P2 M Chromatic Reconstruction floor half le tau  f5e5110d9215: P2 M Chromatic Reconstruction floor half le tau  f5e5110d9215
-- statement:
--   The P2 M Chromatic Reconstruction floor half le tau  f5e5110d9215 construction uses the P2 M Chromatic Reconstruction floor half le tau  f5e5110d9215 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L157-L179
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L157-L179

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem P2M_ChromaticReconstruction_floor_half_le_tau__f5e5110d9215 (k : ℕ) (hk : 4 ≤ k) : ((k / 2 : ℕ) : ℕ∞) ≤ tau k := by sorry

alias «ChromaticReconstruction».«floor_half_le_tau'» := P2M_ChromaticReconstruction_floor_half_le_tau__f5e5110d9215
