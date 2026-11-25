-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_8727189e8376
-- name    : P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_8727189e8376
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:40.861538+00:00
-- url     : https://prove2.me/theorems/4fffa788-5d1b-445e-a004-f047fd2a071e
-- title:
--   P2 M Ground Theory Heights  Heights Inter ar Int mul 8727189e8376: P2 M Ground Theory Heights  Heights Inter ar Int mul 8727189e8376
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter ar Int mul 8727189e8376 construction uses the P2 M Ground Theory Heights  Heights Inter ar Int mul 8727189e8376 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArIntMul.lean#L14-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ArIntMul.lean#L14-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PConsequences
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArIntMul
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_8727189e8376 (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) L = arInt P s A L + arInt P t B L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«arInt_mul» := P2M_GroundTheory_Heights__Heights_Inter_arInt_mul_8727189e8376
