-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_map_bd_eq_span
-- name    : ReciprocityTheory.AnForm.R.WMult.map_bd_eq_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:07.158823+00:00
-- url     : https://prove2.me/theorems/75426ab6-c5b2-5a6f-8dee-ad81c722c67b
-- title:
--   WMult: map bd eq span
-- statement:
--   The WMult construction uses the map bd eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean#L34-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultB.lean#L34-L66

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

theorem ReciprocityTheory.AnForm.R.WMult.map_bd_eq_span {m : ℕ} {I bd : Ideal (MvPolynomial (Fin m) ℂ)} {p : Fin m → ℂ} {e rc : ℕ}
    (S : SncData I bd p e rc) :
    Ideal.map (algebraMap _ (locRing I p)) bd =
      Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by sorry
