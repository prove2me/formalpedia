-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_quotient_dim_le_one_99e9070a5a50
-- name    : P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_quotient_dim_le_one_99e9070a5a50
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:28.751806+00:00
-- url     : https://prove2.me/theorems/7720cf02-5554-4409-bf3e-159c3797a360
-- title:
--   P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski quotient dim le one 99e9070a5a50: P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski quotient dim le one 99e9070a5a50
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski quotient dim le one 99e9070a5a50 construction uses the P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski quotient dim le one 99e9070a5a50 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimUpperZariski.lean#L63-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimUpperZariski.lean#L63-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimUpperZariski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_quotient_dim_le_one_99e9070a5a50 {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLocalDimUpperZariski».«quotient_dim_le_one» := P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_quotient_dim_le_one_99e9070a5a50
