-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_move
-- name    : ReciprocityTheory.ChartRestriction.G.SA.move
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:09.011498+00:00
-- url     : https://prove2.me/theorems/54255a99-657b-4a83-8812-4e2a8f3272a2
-- title:
--   SA: move
-- statement:
--   The SA construction uses the move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SUEqClosure.lean#L21-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SUEqClosure.lean#L21-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SUEqClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
  (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
include hσ hJ he hff hef hfix h2i hδ hσδ

theorem ReciprocityTheory.ChartRestriction.G.SA.move {s : ℕ} {a : Fin s → ι → K} (hae : ∀ j, hf σ J (a j) e = 0)
    (haf : ∀ j, hf σ J (a j) f = 0) (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal →
      m₂.IsMaximal → m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hν : IsUnit (hf σ J b b)) :
    Reach σ J e f a b (e + (hf σ J b b * i2) • f) := by sorry
