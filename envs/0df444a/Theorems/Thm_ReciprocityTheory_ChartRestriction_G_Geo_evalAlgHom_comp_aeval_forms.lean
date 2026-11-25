-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_evalAlgHom_comp_aeval_forms
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.evalAlgHom_comp_aeval_forms
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:26.359115+00:00
-- url     : https://prove2.me/theorems/aa19bac0-f9b6-49d6-a3a8-6e24db467422
-- title:
--   Geo: eval Alg Hom comp aeval forms
-- statement:
--   The Geo construction uses the eval Alg Hom comp aeval forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushC.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushC.lean#L74-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.evalAlgHom_comp_aeval_forms {F : Type} (Q : F → Ideal (MRing ι))
    {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) (W : F) :
    (Pi.evalAlgHom ℚ (fun W : F => MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal (Q W)) W).comp
        (aeval (forms (fun t W => segQ (Q W) t) L)) = aeval (forms (segQ (Q W)) L) := by sorry
