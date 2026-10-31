-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_6
-- name    : PersuasionNetworks.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:58.232071+00:00
-- url     : https://prove2.me/theorems/b628e1f8-ec20-4e6f-af17-5b9c3e3c503f
-- title:
--   Lemma 6 — quantile formula for a conditional mean
-- statement:
--   Let $T$ have law $\mu$ and absolutely continuous distribution function $F$. For $q_0<q_1$ in $[0,1]$, the event $A=\{F^{-1}(q_0)\le T\le F^{-1}(q_1)\}$ has probability $q_1-q_0$, and
--   $$
--   \mathbb E\bigl[T\mid F^{-1}(q_0)\le T\le F^{-1}(q_1)\bigr]=\frac{1}{q_1-q_0}\int_{q_0}^{q_1}F^{-1}(x)\,dx .
--   $$
--
--   This turns every conditional mean over a quantile range into an integral of $F^{-1}$. It is how expected states enter the program (OPT).
--
--   **Formalization Note** The comparisons defining $A$ are in the extended reals, so $q_0=0$ and $q_1=1$ are covered even when $F^{-1}$ is infinite there.
--
--   Differences from the source:
--   - reading: T a random variable with an absolutely continuous cdf → also E[|T|] < ∞ and the state space 𝒯, through IsState; reason: these are the standing assumptions of §2, p.9; without integrability the conditional mean need not exist
--   - generalization: the identity for the conditional mean → also the clause P(A) = q₁ − q₀; reason: it shows the conditioning event has positive probability; dropping it gives the printed claim
--   - encoding: F⁻¹(q₀) ≤ T ≤ F⁻¹(q₁) → comparison of real t with extended-real quantiles; reason: F⁻¹ may be ±∞ at q = 0, 1; same event
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Lemma 6, p.40

import Mathlib
import Definitions.Def_PersuasionNetworks_Quantile
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Lemma 6**, Candogan, SSRN 3346144 (preprint), p.40. For `q₀ < q₁` in `[0, 1]`, with
`A = {t | F⁻¹(q₀) ≤ t ≤ F⁻¹(q₁)}`, the event `A` has probability `q₁ - q₀` and
`E[T | A] = (q₁ - q₀)⁻¹ ∫_{q₀}^{q₁} F⁻¹(x) dx`.

**Formalization Note.** The first clause says that the conditioning on the page is well defined. The
comparisons defining `A` are in `EReal`, so `q₀ = 0` and `q₁ = 1` are included. `μ[|A]` is
`ProbabilityTheory.cond μ A`. -/
theorem lemma_6 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ)
    (hμ : IsState μ 𝒯)
    (q₀ q₁ : ℝ) (hq₀ : 0 ≤ q₀) (hq : q₀ < q₁) (hq₁ : q₁ ≤ 1) :
    μ.real {t : ℝ | stateQuantile μ 𝒯 q₀ ≤ (t : EReal) ∧ (t : EReal) ≤ stateQuantile μ 𝒯 q₁} =
        q₁ - q₀ ∧
      ∫ t, t ∂(cond μ {t : ℝ | stateQuantile μ 𝒯 q₀ ≤ (t : EReal) ∧
          (t : EReal) ≤ stateQuantile μ 𝒯 q₁}) =
        1 / (q₁ - q₀) * ∫ x in q₀..q₁, (stateQuantile μ 𝒯 x).toReal := by sorry

end PersuasionNetworks
