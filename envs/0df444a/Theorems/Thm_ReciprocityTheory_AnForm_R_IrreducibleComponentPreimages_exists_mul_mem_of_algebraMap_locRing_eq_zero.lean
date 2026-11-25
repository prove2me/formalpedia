-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_mul_mem_of_algebraMap_locRing_eq_zero
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:38:33.283143+00:00
-- url     : https://prove2.me/theorems/1b5d4ea9-fb79-5281-ab9a-e4e272612f81
-- title:
--   Irreducible Component Preimages: exists mul mem of algebra Map loc Ring eq zero
-- statement:
--   The Irreducible Component Preimages construction uses the exists mul mem of algebra Map loc Ring eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L46-L65

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
variable {m : ℕ}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero (K : Ideal (MvPolynomial (Fin m) ℂ))
    (p : Fin m → ℂ) {t : MvPolynomial (Fin m) ℂ} (ht : algebraMap _ (locRing K p) t = 0) :
    ∃ s, eval p s ≠ 0 ∧ s * t ∈ K := by sorry
