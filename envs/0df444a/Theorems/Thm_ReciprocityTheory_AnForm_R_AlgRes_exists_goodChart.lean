-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_exists_goodChart
-- name    : ReciprocityTheory.AnForm.R.AlgRes.exists_goodChart
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:21.373472+00:00
-- url     : https://prove2.me/theorems/36db27c9-341d-4ef7-94a6-6b219c2e9e23
-- title:
--   Alg Res: exists good Chart
-- statement:
--   The Alg Res construction uses the exists good Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L88-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L88-L174

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

theorem ReciprocityTheory.AnForm.R.AlgRes.exists_goodChart (R : AlgRes ι P D e) (i : Fin R.n) (x : R.M) (hx : x ∈ R.src i)
    (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ)
    (hr : Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
      Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)))
    (O : Set R.M) (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), R.GoodChart ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y) := by sorry
