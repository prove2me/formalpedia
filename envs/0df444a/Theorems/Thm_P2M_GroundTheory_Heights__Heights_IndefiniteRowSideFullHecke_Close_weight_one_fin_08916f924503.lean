-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_fin_08916f924503
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_fin_08916f924503
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:21.258924+00:00
-- url     : https://prove2.me/theorems/7320a712-899a-44c2-a632-e6515b9032ab
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one fin 08916f924503: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one fin 08916f9245
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one fin 08916f924503 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close weight one fin 08916f924503 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L35-L36

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_fin_08916f924503 {r : ℕ} (d : Fin r →₀ ℕ) : Finsupp.weight 1 d = ∑ i, d i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«weight_one_fin» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_fin_08916f924503
