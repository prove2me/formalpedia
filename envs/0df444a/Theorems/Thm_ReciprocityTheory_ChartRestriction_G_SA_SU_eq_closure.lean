-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_SU_eq_closure
-- name    : ReciprocityTheory.ChartRestriction.G.SA.SU_eq_closure
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:04.228115+00:00
-- url     : https://prove2.me/theorems/fee5870d-34d0-5a42-b4eb-eaa36d753427
-- title:
--   SA: SU eq closure
-- statement:
--   The SA construction uses the SU eq closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SUEqClosure.lean#L170-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SUEqClosure.lean#L170-L261

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

theorem ReciprocityTheory.ChartRestriction.G.SA.SU_eq_closure (hdet : IsUnit J.det) [Nontrivial K]
    (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂) :
    SU σ J = (Submonoid.closure (eichSet σ J e f) : Set (Matrix ι ι K)) := by sorry
