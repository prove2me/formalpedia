-- Prove2me | Theorems.Thm_TargetGranularity_SdVsMd_lemma_3
-- name    : TargetGranularity.SdVsMd.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:46.583402+00:00
-- url     : https://prove2.me/theorems/41652b9d-d4b9-4c8d-aca8-5e389764ff12
-- title:
--   Lemma 3, pp. 17–18 (PDF 18–19) — under md targeting the click set is [0,1] minus an interval, symmetric about 1/2 when the expected targeting set is symmetric
-- statement:
--   Consider the multidimensional environment with price $p\in(0,1)$ and click cost $c_{click}>0$. Let $\widetilde\Sigma\subseteq[0,1]^2$ be a measurable expected targeting set of positive area and let $\Omega^{md}(\widetilde\Sigma)$ be its click set. Then:
--
--   1. there are real numbers $\underline\omega\le\overline\omega$ with $\Omega^{md}(\widetilde\Sigma)=\{\omega\in[0,1]:\omega\le\underline\omega\ \text{or}\ \omega\ge\overline\omega\}$;
--   2. if $\widetilde\Sigma\in\mathcal S$ and symmetric, i.e. $\widetilde\Sigma=\Sigma^{md}(\gamma_1,\gamma_2)$ of Equation (6) with $\gamma_1,\gamma_2\le0$ and $\gamma_1\gamma_2=1$, there is a real $\underline\omega$ with
--   $$\Omega^{md}(\widetilde\Sigma)=\{\omega\in[0,1]:\ \omega\le\underline\omega\ \text{or}\ \omega\ge1-\underline\omega\}.$$
--
--   The second part says that a symmetric targeting strategy induces a click set symmetric about $\omega=1/2$, which reduces the symmetric md equilibrium to a single threshold.
--
--   **Formalization Note** The symmetry part carries the page's hypothesis $\widetilde\Sigma\in\mathcal S$ with $\gamma_1\gamma_2=1$ (as the binder `S = mdSet p γ₁ γ₂`). The thresholds are arbitrary reals, as in Lemma 1, so the empty click set is covered; the page's $0\le\underline\omega\le\overline\omega\le1$ cannot express it.
-- source:
--   Despotakis & Yu, Multidimensional Targeting and Consumer Response, SSRN 3900394 (version of October 11, 2022), pp. 17–18 (PDF 18–19), Lemma 3

import Mathlib
import Definitions.Def_TargetGranularity_SdVsMd_Model

namespace TargetGranularity.SdVsMd

/-- Lemma 3, pp. 17–18: under md targeting, for every non-null measurable expected targeting set
`Σ̃ ⊆ [0,1]²`, the click set is `{ω ∈ [0,1] | ω ≤ ω̲ ∨ ω̄ ≤ ω}` for some reals `ω̲ ≤ ω̄`; and if
`Σ̃ ∈ 𝒮` is symmetric, i.e. `Σ̃ = Σ^md(γ₁, γ₂)` with `γ₁, γ₂ ≤ 0` and `γ₁ · γ₂ = 1`, it is
`{ω ∈ [0,1] | ω ≤ ω̲ ∨ 1 − ω̲ ≤ ω}`. -/
theorem lemma_3 (p cclick : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hcclick : 0 < cclick)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) (hSsub : S ⊆ unitSq)
    (hSpos : 0 < MeasureTheory.volume S) :
    (∃ ωlo ωhi : ℝ, ωlo ≤ ωhi ∧
      mdClick p cclick S = {ω ∈ Set.Icc (0 : ℝ) 1 | ω ≤ ωlo ∨ ωhi ≤ ω}) ∧
    (∀ γ₁ γ₂ : ℝ, γ₁ ≤ 0 → γ₂ ≤ 0 → γ₁ * γ₂ = 1 → S = mdSet p γ₁ γ₂ →
      ∃ ωlo : ℝ, mdClick p cclick S = {ω ∈ Set.Icc (0 : ℝ) 1 | ω ≤ ωlo ∨ 1 - ωlo ≤ ω}) := by sorry

end TargetGranularity.SdVsMd
