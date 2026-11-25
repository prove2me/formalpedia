-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_rsp_iff
-- name    : ReciprocityTheory.AnForm.R.AffPres.rsp_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:06.208222+00:00
-- url     : https://prove2.me/theorems/7230d3c5-d506-5b4f-bfc1-dd617410e8fe
-- title:
--   Aff Pres: rsp iff
-- statement:
--   The Aff Pres construction uses the rsp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L226-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L226-L245

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)

theorem ReciprocityTheory.AnForm.R.AffPres.rsp_iff (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) {e : ℕ} (r : Fin e → W.presheaf.stalk x) :
    FinalTheorems.Rsp (W.presheaf.stalk x) e r ↔
      Ideal.span (Set.range fun l => P.stalkEquiv x hx hc (r l)) =
        Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) ∧
      (e : WithBot ℕ∞) = ringKrullDim (locRing P.K (P.coord x hx)) := by sorry
