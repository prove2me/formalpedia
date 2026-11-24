-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_eval_bind_one
-- name    : ReciprocityTheory.AnForm.R.eval_bind_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:16.203532+00:00
-- url     : https://prove2.me/theorems/dd3d3ffb-f89b-42b3-af3c-58c188a656b8
-- title:
--   R: eval bind one
-- statement:
--   The R construction uses the eval bind one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L11-L16

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
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.R.eval_bind_one {m : ℕ} (y : Fin m → ℂ) {τ : Type} (g : τ → MvPolynomial (Fin m) ℂ)
    (φ : MvPolynomial τ ℂ) : eval y (bind₁ g φ) = eval (fun q => eval y (g q)) φ := by sorry
