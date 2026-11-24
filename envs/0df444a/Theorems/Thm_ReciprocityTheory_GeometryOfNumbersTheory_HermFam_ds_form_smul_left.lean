-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_form_smul_left
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:40.067459+00:00
-- url     : https://prove2.me/theorems/d3080242-805f-4be1-a870-dd21746a25b0
-- title:
--   Herm Fam: ds form smul left
-- statement:
--   The Herm Fam construction uses the ds form smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L105-L107

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_smul_left (h : HermFam K V) (σ : K →+* ℂ) (a : K) (x y : V) :
    h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by sorry
