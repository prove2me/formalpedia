-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_coord_mem_zero
-- name    : ReciprocityTheory.AnForm.R.AlgRes.coord_mem_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:05:36.990294+00:00
-- url     : https://prove2.me/theorems/8e6d553f-0dac-43a9-b026-f46284bbf52e
-- title:
--   Alg Res: coord mem zero
-- statement:
--   The Alg Res construction uses the coord mem zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L127-L132

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.AlgRes.coord_mem_zero {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (i : Fin R.n) {x : R.M} (hx : x ∈ R.src i) :
    ∀ g ∈ R.ideal i, eval (R.coord i x) g = 0 := by sorry
