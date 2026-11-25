-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_points_rename_fbb12ff9318c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_points_rename_fbb12ff9318c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:18.370029+00:00
-- url     : https://prove2.me/theorems/2037c16a-f5f9-4070-bc3a-9ec321bb6aa3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall points rename fbb12ff9318c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall points renam
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall points rename fbb12ff9318c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall points rename fbb12ff9318c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L223-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L223-L230

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_points_rename_fbb12ff9318c (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    (∀ z ∈ P.points ℂ, ‖evalCone z (rename (Heights.blockIncl k₀)
        (rename (blockCoordEquiv (n := n) k₀) f))‖ ≤ B * l2Norm (z k₀) ^ N) ↔
      ∀ z ∈ P.points ℂ, ‖eval₂ (Int.castRingHom ℂ) (z k₀) f‖ ≤ B * l2Norm (z k₀) ^ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«forall_points_rename» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_points_rename_fbb12ff9318c
