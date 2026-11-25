-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_nbhd_zeroLocus
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_nbhd_zeroLocus
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:43.744155+00:00
-- url     : https://prove2.me/theorems/bd5096d3-7ca6-4ec8-a959-610410dd278c
-- title:
--   Irreducible Component Preimages: exists nbhd zero Locus
-- statement:
--   The Irreducible Component Preimages construction uses the exists nbhd zero Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L154-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L154-L184

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_nbhd_zeroLocus {U V : W.Opens} {x : W} (hxU : x ∈ U) (hxV : x ∈ V) (s : Γ(W, U))
    (s' : Γ(W, V)) (u : W.presheaf.stalk x) (hu : IsUnit u)
    (heq : W.presheaf.germ V x hxV s' = W.presheaf.germ U x hxU s * u) :
    ∃ O : W.Opens, x ∈ O ∧ ∀ z ∈ O, (z ∈ W.zeroLocus {s} ↔ z ∈ W.zeroLocus {s'}) := by sorry
