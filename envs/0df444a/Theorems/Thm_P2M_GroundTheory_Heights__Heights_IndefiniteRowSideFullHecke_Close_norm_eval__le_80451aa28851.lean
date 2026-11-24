-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_norm_eval__le_80451aa28851
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_norm_eval__le_80451aa28851
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:17.457621+00:00
-- url     : https://prove2.me/theorems/47a9e9c2-e553-42df-99f9-00eb5ff70cc7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close norm eval  le 80451aa28851: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close norm eval  le 80451aa28851
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close norm eval  le 80451aa28851 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close norm eval  le 80451aa28851 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L142-L154

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
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_norm_eval__le_80451aa28851 {r N : ℕ} (f : MvPolynomial (Fin r) ℤ) (hf : f.IsHomogeneous N)
    (w : Fin r → ℂ) :
    ‖eval₂ (Int.castRingHom ℂ) w f‖ ≤
      (∑ d ∈ f.support, ‖Int.castRingHom ℂ (f.coeff d)‖) * l2Norm w ^ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«norm_eval₂_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_norm_eval__le_80451aa28851
