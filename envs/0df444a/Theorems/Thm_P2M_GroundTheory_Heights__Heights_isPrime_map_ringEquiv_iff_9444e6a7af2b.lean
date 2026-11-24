-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
-- name    : P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:02.813136+00:00
-- url     : https://prove2.me/theorems/5784ebb8-2dd0-46df-a8ad-8b8c7b9013f8
-- title:
--   P2 M Ground Theory Heights  Heights is Prime map ring Equiv iff 9444e6a7af2b: P2 M Ground Theory Heights  Heights is Prime map ring Equiv iff 9444e6a7af2b
-- statement:
--   The P2 M Ground Theory Heights  Heights is Prime map ring Equiv iff 9444e6a7af2b construction uses the P2 M Ground Theory Heights  Heights is Prime map ring Equiv iff 9444e6a7af2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L18-L24

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

theorem P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b (V : Ideal A) : (V.map σ).IsPrime ↔ V.IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isPrime_map_ringEquiv_iff» := P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
