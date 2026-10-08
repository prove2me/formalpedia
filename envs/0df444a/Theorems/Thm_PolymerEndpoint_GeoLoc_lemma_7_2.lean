-- Prove2me | Theorems.Thm_PolymerEndpoint_GeoLoc_lemma_7_2
-- name    : PolymerEndpoint.GeoLoc.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:34:17.993425+00:00
-- url     : https://prove2.me/theorems/e6c1374a-543d-455d-b883-2fba82e5e964
-- title:
--   Lemma 7.2, p. 47 — if β > β_c then ∫ Q(f) ν(df) = ∞ for every ν ∈ 𝓜
-- statement:
--   Let $d\ge1$, $\mathfrak L$ non-degenerate with (1.1), and assume $\beta>\beta_c$. Then for any $\nu\in\mathcal M$,
--   $$\int Q(f)\,\nu(df)=\infty,$$
--   where $Q(f)=\sum_n q_n(f)/(1-q_n(f))$ and $\mathcal M$ is the set of minimisers of $\mathcal R$ over the fixed points of the update map (4.8).
--
--   The lemma shows that at low temperature the limiting endpoint distributions cannot spread their mass over many copies of $\mathbb Z^d$ in a summable way; it gives the positivity $\inf_{\nu\in\mathcal M}\nu(m>1-\delta)>0$ in the proof of Theorem 7.3(a).
--
--   **Formalization Note.** The integral is the lower Lebesgue integral of the $[0,\infty]$-valued function $Q$. $\beta>\beta_c$ is encoded as $\lim\mathbf E(F_n)<\lambda(\beta)$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 47, Lemma 7.2

import Mathlib
import Definitions.Def_PolymerEndpoint_GeoLoc_Update
import Definitions.Def_PolymerEndpoint_GeoLoc_Functionals
open MeasureTheory ProbabilityTheory

namespace PolymerEndpoint.GeoLoc

/-- Lemma 7.2: if `β > β_c`, then `∫ Q(f) ν(df) = ∞` for every `ν ∈ 𝓜`. -/
theorem lemma_7_2 (d : ℕ) (hd : 1 ≤ d) (𝔏 : Measure ℝ) [IsProbabilityMeasure 𝔏]
    (h𝔏 : ∀ c : ℝ, 𝔏 ≠ Measure.dirac c) (β : ℝ) (hβ : 0 ≤ β)
    (hmgf : ∀ α ∈ Set.Icc (-2 * β) (2 * β), Integrable (fun x => Real.exp (α * x)) 𝔏) (hlow : LowTemp d 𝔏 β) :
    ∀ ν ∈ M d 𝔏 β, ∫⁻ f, Qfun f ∂ν = ⊤ := by sorry

end PolymerEndpoint.GeoLoc
