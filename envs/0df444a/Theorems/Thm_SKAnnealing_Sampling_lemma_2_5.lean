-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_2_5
-- name    : SKAnnealing.Sampling.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:29.327196+00:00
-- url     : https://prove2.me/theorems/703f3eee-ba29-4aa5-b98a-c8c85b0449c7
-- title:
--   Lemma 2.5, p. 12 — contiguity of the null and planted SK models: $c\,\mu_{\mathrm{pl}}(\mathcal E)^2\le\mu_{\mathrm{null}}(\mathcal E)\le C\sqrt{\mu_{\mathrm{pl}}(\mathcal E)}$
-- statement:
--   Let $0\le\beta<1$. Let $\mu_{\mathrm{null}}$ be the law of the Gibbs measure of $H_{\mathrm{null}}(\sigma)=\frac\beta2\sigma^\top W\sigma$ with $W\sim\mathrm{GOE}(N)$, and $\mu_{\mathrm{pl}}$ the law of the Gibbs measure of
--   $$H_{\mathrm{pl}}(\sigma)=\frac\beta2\,\sigma^\top W\sigma+\frac{\beta^2}{2N}\langle\sigma,x\rangle^2,$$
--   with $W\sim\mathrm{GOE}(N)$ and $x\sim\mathrm{Unif}\{\pm1\}^N$ independent. Both are laws on the space of probability measures on $\{\pm1\}^N$.
--
--   **Lemma 2.5.** There are constants $c>0$ and $C>0$, depending only on $\beta$, such that for every $N$ and every event $\mathcal E$ over the space of measures on $\{\pm1\}^N$,
--   $$c\,\mu_{\mathrm{pl}}(\mathcal E)^2\ \le\ \mu_{\mathrm{null}}(\mathcal E)\ \le\ C\sqrt{\mu_{\mathrm{pl}}(\mathcal E)} .$$
--   In particular the two laws are mutually contiguous.
--
--   This lets every high-probability statement proved for the planted model (Theorem 1.4, display (7), Lemma 1.5) transfer to the SK model itself, with a polynomial loss in the failure probability.
--
--   Differences from the source:
--   - encoding: the law over measures and an event 𝓔 over the space of measures → µ_null(𝓔) = P_W(gibbs(βW) ∈ 𝓔) and µ_pl(𝓔) = P_{W,x}(gibbs(H_pl) ∈ 𝓔) for every measurable set 𝓔 of functions {±1}^N → ℝ; reason: the pushforward evaluated on preimages; a measure on the finite cube is its weight function, and an event is a measurable set
--   - reading: constants c, C → c > 0 and C > 0 depending only on β, the same for every N; reason: with c ≤ 0 the first inequality is empty; the paper's constants are uniform in N, and for each fixed N both inequalities hold by Cauchy–Schwarz with finite moments, so no N₀ is needed
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 2.5, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_plantedTilted

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 2.5** (contiguity of the null and planted models). Let `0 ≤ β < 1`. `µ_null` is the law of the
Gibbs measure of `H_null(σ) = (β/2) σᵀWσ`, `W ∼ GOE(N)`; `µ_pl` is the law of the Gibbs measure of
`H_pl(σ) = (β/2) σᵀWσ + (β²/(2N))⟨σ, x⟩²`, `W ∼ GOE(N)`, `x ∼ {±1}^N`. For any event `E` over the space of
measures on `{±1}^N`, `c µ_pl(E)² ≤ µ_null(E) ≤ C √(µ_pl(E))`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 2.5, p. 12 (PDF p. 14).

**Formalization Note** A measure on `{±1}^N` is a function `Spin N → ℝ`; `µ_null(E)` is the `disorderLaw`
probability that `gibbs (β • W) ∈ E`, `µ_pl(E)` the `plantedLaw` probability that
`gibbs (plantedDisorder β W x) ∈ E` (preimage form, so no measurability of the pushforward map is needed). An
event is a measurable `E`. `c, C > 0` depend only on `β` and hold for every `N` ("mutually contiguous" is their
consequence). Reading R8: the diagonal of `W` does not affect either Gibbs measure. -/
theorem lemma_2_5 :
    ∀ β : ℝ, 0 ≤ β → β < 1 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (E : Set (Spin N → ℝ)), MeasurableSet E →
        c * ((plantedLaw N).real {wx | gibbs (plantedDisorder β wx.1 wx.2) ∈ E}) ^ 2
            ≤ (disorderLaw N).real {W | gibbs (β • W) ∈ E} ∧
          (disorderLaw N).real {W | gibbs (β • W) ∈ E}
            ≤ C * Real.sqrt ((plantedLaw N).real {wx | gibbs (plantedDisorder β wx.1 wx.2) ∈ E}) := by sorry

end SKAnnealing.Sampling
