-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_form_sum_left
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_sum_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:08:54.219107+00:00
-- url     : https://prove2.me/theorems/97592a6f-7418-4aed-b4df-943bd96f8b93
-- title:
--   Herm Fam: ds form sum left
-- statement:
--   The Herm Fam construction uses the ds form sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L100-L103

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_form_sum_left (h : HermFam K V) (σ : K →+* ℂ) (y : V) {ι : Type*}
    (s : Finset ι) (f : ι → V) : h.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, h.form σ (f i) y := by sorry
