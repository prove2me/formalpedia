-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:52.301952+00:00
-- url     : https://prove2.me/theorems/3aed3133-2ff8-4a4c-bee8-93bdd1db6768
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient map 34db07ffdc36: P2 M Ground Theory Heights  Heights ring Krull Dim quotient map 34db07ffdc36
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient map 34db07ffdc36 construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient map 34db07ffdc36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L31-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36 (V : Ideal A) :
    ringKrullDim (A' ⧸ V.map σ) = ringKrullDim (A ⧸ V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_map» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_map_34db07ffdc36
