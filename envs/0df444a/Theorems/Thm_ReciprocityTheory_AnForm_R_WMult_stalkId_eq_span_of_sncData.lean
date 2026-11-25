-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_stalkId_eq_span_of_sncData
-- name    : ReciprocityTheory.AnForm.R.WMult.stalkId_eq_span_of_sncData
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:11:10.509886+00:00
-- url     : https://prove2.me/theorems/438325fe-eaf6-4550-a4d5-0159ed9193ea
-- title:
--   WMult: stalk Id eq span of snc Data
-- statement:
--   The WMult construction uses the stalk Id eq span of snc Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean#L68-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean#L68-L92

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory MvPolynomial
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.WMult.stalkId_eq_span_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.stalkId Z x = Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))} := by sorry
