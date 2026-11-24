-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be
-- name    : P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:55.587309+00:00
-- url     : https://prove2.me/theorems/9689a5aa-4897-43ca-b6ca-f011aa899ef1
-- title:
--   P2 M Ground Theory Heights  Heights map ring Equiv injective a552ea8108be: P2 M Ground Theory Heights  Heights map ring Equiv injective a552ea8108be
-- statement:
--   The P2 M Ground Theory Heights  Heights map ring Equiv injective a552ea8108be construction uses the P2 M Ground Theory Heights  Heights map ring Equiv injective a552ea8108be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be : Function.Injective (Ideal.map σ : Ideal A → Ideal A') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«map_ringEquiv_injective» := P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be
