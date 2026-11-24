-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_analyticAt_coord_symm
-- name    : ReciprocityTheory.AnForm.R.AlgRes.analyticAt_coord_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:23.944751+00:00
-- url     : https://prove2.me/theorems/5538f93b-2afa-42f9-af98-9ec7c92acefd
-- title:
--   Alg Res: analytic At coord symm
-- statement:
--   The Alg Res construction uses the analytic At coord symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L32-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean#L32-L68

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

theorem ReciprocityTheory.AnForm.R.AlgRes.analyticAt_coord_symm (R : AlgRes ι P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} {i : Fin R.n} (hs : ψ.source ⊆ R.src i)
    {g : (Fin e → ℂ) → Fin (R.amb i) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target)
    (hgc : ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w)
    (j : Fin R.n) (h : MvPolynomial (Fin (R.amb j)) ℂ) {w : Fin e → ℂ} (hw : w ∈ ψ.target)
    (hwj : ψ.symm w ∈ R.src j) :
    AnalyticAt ℂ (fun w => eval (R.coord j (ψ.symm w)) h) w := by sorry
