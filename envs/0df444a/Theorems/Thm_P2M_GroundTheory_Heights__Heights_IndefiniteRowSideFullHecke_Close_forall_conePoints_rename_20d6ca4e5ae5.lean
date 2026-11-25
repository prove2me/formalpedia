-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_conePoints_rename_20d6ca4e5ae5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_conePoints_rename_20d6ca4e5ae5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:28.65196+00:00
-- url     : https://prove2.me/theorems/7fc53a41-fe51-4244-937b-4cc3a3eeb26b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall cone Points rename 20d6ca4e5ae5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall cone Po
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall cone Points rename 20d6ca4e5ae5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close forall cone Points rename 20d6ca4e5ae5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L234-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L234-L252

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_conePoints_rename_20d6ca4e5ae5 (P : ArithVariety n) (k₀ : ι) (N : ℕ)
    (f : MvPolynomial (Fin (n k₀ + 1)) ℤ) (B : ℝ) :
    (∀ z' ∈ Heights.conePoints (P.projIdeal k₀) ℂ,
        ‖evalCone z' (rename (blockCoordEquiv (n := n) k₀) f)‖ ≤ B * l2Norm (z' ()) ^ N) ↔
      ∀ w ∈ oneBlockPoints P k₀, ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤ B * l2Norm w ^ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«forall_conePoints_rename» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_forall_conePoints_rename_20d6ca4e5ae5
