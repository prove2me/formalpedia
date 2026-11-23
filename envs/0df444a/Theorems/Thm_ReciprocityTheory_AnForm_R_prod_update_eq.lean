-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_prod_update_eq
-- name    : ReciprocityTheory.AnForm.R.prod_update_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:57.000802+00:00
-- url     : https://prove2.me/theorems/861f7348-b898-4ce5-b140-3b875d2df131
-- title:
--   R: prod update eq
-- statement:
--   The R construction uses the prod update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L32-L39

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.prod_update_eq {M : Type*} [CommMonoid M] [DecidableEq K] (x : (Σ k, ι k) → M)
    (p : (k : K) → ι k) (k : K) (v : ι k) :
    ∏ j, x ⟨j, Function.update p k v j⟩ = x ⟨k, v⟩ * ∏ j ∈ Finset.univ.erase k, x ⟨j, p j⟩ := by sorry
