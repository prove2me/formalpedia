-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_segreMap_aeval_update
-- name    : ReciprocityTheory.AnForm.R.segreMap_aeval_update
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:22.655959+00:00
-- url     : https://prove2.me/theorems/4ca10ae4-cddb-43c8-9e64-723fedc6d3ba
-- title:
--   R: segre Map aeval update
-- statement:
--   The R construction uses the segre Map aeval update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L85-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L85-L126

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

theorem ReciprocityTheory.AnForm.R.segreMap_aeval_update [DecidableEq K] (p : (k : K) → ι k) {f : MvPolynomial (Σ k, ι k) ℂ}
    {a : K → ℕ} (hf : IsMultiHomog f a) :
    segreMap (aeval (fun q : Σ k, ι k => (X (Function.update p q.1 q.2) :
        MvPolynomial ((k : K) → ι k) ℂ)) f) =
      (∏ k, (∏ j ∈ Finset.univ.erase k, (X ⟨j, p j⟩ : MvPolynomial (Σ k, ι k) ℂ)) ^ a k) * f := by sorry
