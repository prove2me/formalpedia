-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:25:28.972802+00:00
-- url     : https://prove2.me/theorems/21ece8f2-cbeb-405a-b2ab-924bc0e429e5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close exists rename of block 6c006f28b61f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close exists rename of
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close exists rename of block 6c006f28b61f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close exists rename of block 6c006f28b61f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L54-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L54-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f (k₀ : ι) (m : ℕ) (f : MvPolynomial (Coord n) ℤ)
    (hf : IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1)) :
    ∃ g : MvPolynomial (Fin (n k₀ + 1)) ℤ, g.IsHomogeneous m ∧
      rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) g = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«exists_rename_of_block» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exists_rename_of_block_6c006f28b61f
