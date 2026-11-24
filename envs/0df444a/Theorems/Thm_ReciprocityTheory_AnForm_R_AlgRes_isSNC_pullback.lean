-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_isSNC_pullback
-- name    : ReciprocityTheory.AnForm.R.AlgRes.isSNC_pullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:27.281124+00:00
-- url     : https://prove2.me/theorems/decd8120-1f75-427d-a792-bf82d5e0fae5
-- title:
--   Alg Res: is SNC pullback
-- statement:
--   The Alg Res construction uses the is SNC pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L134-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SNCstep.lean#L134-L227

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

theorem ReciprocityTheory.AnForm.R.AlgRes.isSNC_pullback {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A)
    (idx : R.M → Fin R.n) (hidx : ∀ x, x ∈ R.src (idx x)) (φ : R.M → R.M → ℝ)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a) (hfP : f ∉ P)
    (hz : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ m : Fin R.rc → ℕ,
      IsSNC A ⟨fun x => R.src (idx x), fun x => R.isOpen_alt_bis (idx x), hidx, φ⟩
        (fun x y => eval (fun q => eval (R.coord (idx x) y) (R.lift (idx x) q)) f) m R.comp := by sorry
