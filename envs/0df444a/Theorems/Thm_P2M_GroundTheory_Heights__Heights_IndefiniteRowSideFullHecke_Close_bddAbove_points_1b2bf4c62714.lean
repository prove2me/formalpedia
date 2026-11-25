-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_points_1b2bf4c62714
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_points_1b2bf4c62714
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:11.455678+00:00
-- url     : https://prove2.me/theorems/01b9e631-c6d5-4e05-9128-1b0d719d83bb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above points 1b2bf4c62714: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above points 1b2bf4
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above points 1b2bf4c62714 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above points 1b2bf4c62714 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L208-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L208-L212

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_points_1b2bf4c62714 (P : ArithVariety n) (k₀ : ι) {N : ℕ}
    {f : MvPolynomial (Fin (n k₀ + 1)) ℤ} (hf : f.IsHomogeneous N) :
    BddAbove ((fun z : Cone n ℂ ↦
        ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ / (pullFS n k₀).metric z ^ N) '' P.points ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«bddAbove_points» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_points_1b2bf4c62714
