-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_top_le_zero
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.top_le_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:31.789523+00:00
-- url     : https://prove2.me/theorems/98abc987-6fe4-4bc7-9e36-db02437479cb
-- title:
--   Semi Pt: top le zero
-- statement:
--   The Semi Pt construction uses the top le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean#L44-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegI.lean#L44-L148

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.top_le_zero (hN : IntegralIndexStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (j p : Fin r) (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K))
    (hGj : Gj.FG) (hGp : Gp.FG) (hj : ∀ x ∈ Gj, IsAt j x) (hp : ∀ x ∈ Gp, IsAt p x)
    (hpair : ∀ x ∈ Gj, ∀ y ∈ Gp, IsIntegralElt (S.c (x j) * y p))
    (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hx0j : x0 j ≠ 0) (hy : y ∈ Gp) (hyp : y p ≠ 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (d : ℝ) (hd : 0 < d) (hδj : ∀ σ, δ σ j = d)
    (hδp : ∀ σ, δ σ p = d⁻¹) (h0 : latDeg (diagMet δ) Gj ![x0] = 0) :
    latDeg (diagMet δ) Gp ![y] ≤ 0 := by sorry
