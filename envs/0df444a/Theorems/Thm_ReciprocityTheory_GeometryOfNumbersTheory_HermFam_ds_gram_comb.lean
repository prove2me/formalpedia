-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_HermFam_ds_gram_comb
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_gram_comb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:37.416227+00:00
-- url     : https://prove2.me/theorems/e8f614c2-4b6e-40d2-a0e2-50ae5caf95ea
-- title:
--   Herm Fam: ds gram comb
-- statement:
--   The Herm Fam construction uses the ds gram comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L109-L117

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.HermFam.ds_gram_comb (h : HermFam K V) (σ : K →+* ℂ) {r : ℕ} (v : Fin r → V)
    (G : Matrix (Fin r) (Fin r) K) :
    h.gram σ (fun j => ∑ i, G i j • v i) = (G.map σ)ᴴ * h.gram σ v * G.map σ := by sorry
