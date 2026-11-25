-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_freq_entry
-- name    : ReciprocityTheory.ChartRestriction.G.FD.DataX.freq_entry
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:27.41681+00:00
-- url     : https://prove2.me/theorems/0f91479c-d494-422c-844c-4f1c5bcb7d57
-- title:
--   Data X: freq entry
-- statement:
--   The Data X construction uses the freq entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L153-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L153-L167

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.DataX.freq_entry (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hf : X.IsFreqZ X.g χ) (z : X.Ψ → ℂ)
    (w : 𝓞 E → Fin 2 → Fin 2 → E) (hwi : ∀ γ i k, IsIntegral ℤ (w γ i k))
    (hwh : ∀ γ i k, cc (w γ i k) = w γ k i)
    (hterm : ∀ γ : 𝓞 E, (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w γ i k)).re =
      2 * (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by sorry
