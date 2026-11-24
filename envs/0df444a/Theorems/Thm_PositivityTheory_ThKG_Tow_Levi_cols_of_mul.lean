-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_cols_of_mul
-- name    : PositivityTheory.ThKG.Tow.Levi.cols_of_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:08.327957+00:00
-- url     : https://prove2.me/theorems/cbeb2ec1-421e-474f-b5c6-a572b96f0d87
-- title:
--   Levi: cols of mul
-- statement:
--   The Levi construction uses the cols of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/TowerModels/LeviAlg.lean#L56-L65

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
omit [DecidableEq d] [DecidableEq e]

theorem PositivityTheory.ThKG.Tow.Levi.cols_of_mul {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by sorry
