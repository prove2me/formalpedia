-- Prove2me | Theorems.Thm_TabooRegen_Supplement_theorem_1
-- name    : TabooRegen.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:43:13.089701+00:00
-- url     : https://prove2.me/theorems/30124364-05f4-47b5-81db-bfb115c526ff
-- title:
--   Theorem 1 — given $\Gamma>t+s$, the post-$t$ process converges uniformly to the forward taboo limit
-- statement:
--   Let $X$ be taboo-regenerative in the wide sense with $T(0)=0$ (no delay), and suppose that $X$ satisfies A1–A4 with constant $\alpha\ge0$. For $t\ge0$ let $X_t=(X(t+s):s\ge0)$ be the post-$t$ process, a random element of the path space $D_{\tilde S}[0,\infty)$ with its σ-algebra $\mathcal D$. Then for every $s\ge0$,
--   $$
--   \lim_{t\to\infty}\ \sup_{B\in\mathcal D}\left|P(X_t\in B\mid\Gamma>t+s)-\frac{E\int_0^{\tau_1}e^{\alpha(u+s)}\,I(X_u\in B,\ \Gamma>u+s)\,du}{E\int_0^{\tau_1\wedge\Gamma}e^{\alpha u}\,du}\right|=0.
--   $$
--
--   The theorem identifies the limit law of the whole future of the process, seen from a late time $t$, given that $X$ has not left $A$ by time $t+s$: it is an explicit regenerative-type ratio over one cycle, the regenerative analogue of the quasi-stationary limit of Markov chains, and the convergence is in total variation over path events.
--
--   Differences from the source:
--   - encoding: complete separable metric space $S$, paths in $D_{\tilde S}[0,\infty)$ with the Skorohod σ-algebra $\mathcal D$ → Polish $S$ with its Borel σ-algebra; the published `Path S` (càdlàg maps into `S ⊕ Unit`, cylinder-trace σ-algebra); reason: the convention of the published `TabooRegen.Model`; the cylinder trace equals the Skorohod Borel σ-algebra for separable metric $\tilde S$
--   - encoding: $\lim_{t\to\infty}\sup_{B\in\mathcal D}|\cdots|=0$ for each $s\ge0$ → for every $s\ge0$ and $\varepsilon>0$, eventually in $t\in[0,\infty)$, for every measurable $B$, $|\cdots|\le\varepsilon$; reason: the same statement; the threshold in $t$ does not depend on $B$
--   - encoding: $P(\cdot\mid\Gamma>t+s)$ and the ratio of expectations → `ProbabilityTheory.cond`; numerator and denominator as extended non-negative integrals, divided after conversion to reals; reason: under A1–A4 the denominator is finite and positive and the numerator is at most $e^{\alpha s}$ times the denominator, so no value changes
--   - encoding: expectations in A1–A4 and the denominator $E\int_0^{\tau_1\wedge\Gamma}e^{\alpha u}du$ → published A1–A4 and `cycleWeight` under $Q=P(\cdot\mid\Gamma\ge T(0))$, $E\int_0^{\gamma_1\wedge\tau_1}e^{\alpha u}du$; reason: with $T(0)=0$, $Q=P$ and $\gamma_1\wedge\tau_1=\Gamma\wedge\tau_1$ (p.276)
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, Theorem 1, p.280 (PDF p.10); proof p.281

import Mathlib
import Definitions.Def_TabooRegen_Supplement_Classical

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen.Supplement

open TabooRegen TabooRegen.Model

/-- **Theorem 1** (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing
Systems 46 (2004), p.280). Let `X` be taboo-regenerative in the wide sense, and suppose `T(0) = 0`.
If `X` satisfies A1–A4, then for every `s ⩾ 0`
`lim_{t→∞} sup_{B∈𝒟} |P(X_t ∈ B | Γ > t + s)
  − E ∫₀^{τ₁} e^{α(u+s)} I(X_u ∈ B, Γ > u + s) du / E ∫₀^{τ₁∧Γ} e^{αu} du| = 0`.

**Formalization Note.**
* `X_t` is the post-`t` path `post M t` (an element of the published `Path S`), and `B` ranges over
  the measurable sets of paths.
* `sup_B |…| → 0` is written `∀ ε > 0`, eventually in `t`, `∀ B` measurable, `|…| ⩽ ε`; `s ⩾ 0` is
  free (`s : ℝ≥0`) and time is `ℝ≥0`.
* `P(· | Γ > t + s)` is `ProbabilityTheory.cond`; the numerator of the limit is the
  `ℝ≥0∞`-valued `forwardNum`, the denominator the published `cycleWeight α`
  (`γ₁ ∧ τ₁ = Γ ∧ τ₁` when `T(0) = 0`). -/
theorem theorem_1 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] {A : Set S} {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)
    (hreg : M.IsWideSenseTabooRegen) (h0 : ∀ ω, M.T 0 ω = 0) {α : ℝ} (h1 : M.A1 α)
    (h2 : M.A2) (h3 : M.A3 α) (h4 : M.A4 α) :
    ∀ s : ℝ≥0, ∀ ε > 0, ∀ᶠ t : ℝ≥0 in atTop, ∀ B : Set (Path S), MeasurableSet B →
      |(ProbabilityTheory.cond M.P {ω | ((t + s : ℝ≥0) : ℝ≥0∞) < M.Γ ω}
          {ω | post M t ω ∈ B}).toReal - forwardLimit M α s B| ≤ ε := by sorry

end TabooRegen.Supplement
