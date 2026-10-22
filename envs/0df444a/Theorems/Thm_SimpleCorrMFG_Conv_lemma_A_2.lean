-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_lemma_A_2
-- name    : SimpleCorrMFG.Conv.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:47.403036+00:00
-- url     : https://prove2.me/theorems/269cdb90-496e-4e26-a7f9-4c9de201785b
-- title:
--   Lemma A.2, p. 28 — converging together: $\mathbb E_n[d_{\mathcal Z}(Z_n,\tilde Z_n)]\to0$ preserves the limit in distribution
-- statement:
--   Let $\mathcal Y,\mathcal Z$ be Polish spaces and $d_{\mathcal Z}$ a metric compatible with the topology of $\mathcal Z$. For each $n$ let $(Y_n,Z_n,\tilde Z_n)$ be a $\mathcal Y\times\mathcal Z\times\mathcal Z$-valued random variable on a probability space $(\Omega_n,\mathcal F_n,P_n)$. Suppose that $(Y_n,Z_n)$ converges in distribution to some $(Y,Z)$ defined on $(\Omega,\mathcal F,P)$ and that
--   $$\mathbb E_n\big[d_{\mathcal Z}(Z_n,\tilde Z_n)\big]\xrightarrow[n\to\infty]{}0.$$
--   Then $(Y_n,\tilde Z_n)$ converges in distribution to $(Y,Z)$.
--
--   The lemma lets the proof of Theorem 6.1 replace the empirical measures of the $N$-player game by those of a decoupled system, and the empirical measure of the others by that of all players.
--
--   **Formalization Note** $d_{\mathcal Z}$ is the distance of a metric-space structure on $\mathcal Z$ inducing its Polish topology; the expectation is a lower Lebesgue integral of the extended distance, so no integrability assumption is needed.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 28, Lemma A.2 (with the standing assumptions of Appendix A, p. 27)

import Mathlib

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Lemma A.2 (p. 28). The metric `d_Z` is the `dist` of a metric space structure inducing the
(Polish) topology of `𝒵`; `E_n[d_Z(Z_n, Z̃_n)]` is a lower Lebesgue integral. -/
theorem lemma_A_2 {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] [MetricSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (Yn : ∀ n, Ω n → 𝒴) (Zn Ztn : ∀ n, Ω n → 𝒵) (hYn : ∀ n, Measurable (Yn n))
    (hZn : ∀ n, Measurable (Zn n)) (hZtn : ∀ n, Measurable (Ztn n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → 𝒴) (Z : Ω' → 𝒵) (hY : Measurable Y) (hZ : Measurable Z)
    (hconv : TendstoInDistribution (fun n ω => (Yn n ω, Zn n ω)) atTop (fun ω => (Y ω, Z ω)) P P')
    (hdist : Tendsto (fun n => ∫⁻ ω, edist (Zn n ω) (Ztn n ω) ∂(P n)) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => (Yn n ω, Ztn n ω)) atTop (fun ω => (Y ω, Z ω)) P P' := by sorry

end SimpleCorrMFG.Conv
