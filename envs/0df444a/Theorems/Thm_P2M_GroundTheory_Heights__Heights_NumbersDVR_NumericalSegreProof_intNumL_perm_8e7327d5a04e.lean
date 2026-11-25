-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_perm_8e7327d5a04e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_perm_8e7327d5a04e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:42.169921+00:00
-- url     : https://prove2.me/theorems/3a404f40-6ebc-48f3-9db1-6878446e06e7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L perm 8e7327d5a04e: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L perm 8e7327d5a04e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L perm 8e7327d5a04e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L perm 8e7327d5a04e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L117-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
variable {K : Type*} [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_perm_8e7327d5a04e {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    {l l' : List (K → ℤ)} (h : l.Perm l') : intNumL F P l = intNumL F P l' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«intNumL_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_perm_8e7327d5a04e
