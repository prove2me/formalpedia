-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_block_isWeightedHomogeneous_56f0bbcc7032
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_block_isWeightedHomogeneous_56f0bbcc7032
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:18.023966+00:00
-- url     : https://prove2.me/theorems/653e9c0e-4f85-5c38-8c1f-130332f5464a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename block is Weighted Homogeneous 56f0bbcc7032: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close ren
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename block is Weighted Homogeneous 56f0bbcc7032 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close rename block is Weighted Homogeneous 56f0bbcc7032 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L76-L92

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_block_isWeightedHomogeneous_56f0bbcc7032 (k₀ : ι) {N : ℕ} {g : MvPolynomial (Fin (n k₀ + 1)) ℤ}
    (hg : g.IsHomogeneous N) :
    IsWeightedHomogeneous (coordDeg n) (rename (fun i ↦ (⟨k₀, i⟩ : Coord n)) g) (N • Pi.single k₀ 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«rename_block_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_rename_block_isWeightedHomogeneous_56f0bbcc7032
