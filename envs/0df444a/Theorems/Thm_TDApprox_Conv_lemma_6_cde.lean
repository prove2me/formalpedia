-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_6_cde
-- name    : TDApprox.Conv.lemma_6_cde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:52.082777+00:00
-- url     : https://prove2.me/theorems/f4f6654d-e7d3-4ca9-8826-ed79581148ee
-- title:
--   Lemma 6(c)–(e), p. 15 — steady-state moments of z_t: E₀[z_tφ′(i_t)], E₀[z_tφ′(i_{t+1})], E₀[z_t g(i_t, i_{t+1})]
-- statement:
--   Under Assumptions 1, 2 and 3, let $(i_t)_{t\in\mathbb Z}$ be the chain in steady state (as in Lemma 6(a)–(b)), let $\lambda \in [0,1]$, and define the steady-state eligibility vector of Eq. (5),
--   $$z_t = \sum_{\tau=-\infty}^t (\alpha\lambda)^{t-\tau}\phi(i_\tau).$$
--   Then, for every $t$, the series defining $z_t$ converges almost surely, the expectations below are well defined and finite, and
--   1. (c) $E_0[z_t\phi'(i_t)] = \sum_{m=0}^\infty (\alpha\lambda)^m\,\Phi DP^m\Phi'$;
--   2. (d) $E_0[z_t\phi'(i_{t+1})] = \sum_{m=0}^\infty (\alpha\lambda)^m\,\Phi DP^{m+1}\Phi'$;
--   3. (e) $E_0[z_t\, g(i_t,i_{t+1})] = \sum_{m=0}^\infty (\alpha\lambda)^m\,\Phi DP^m\bar g$;
--
--   each series on the right converging.
--
--   These are the ingredients of the formula for the mean TD step in Lemma 7.
--
--   **Formalization Note.** $z_t$ is written $\sum_{\tau\ge0}(\alpha\lambda)^\tau\phi(i_{t-\tau})$. Its almost-sure convergence, which the page cites as "well known", is stated as a conjunct. Convergence of the matrix series is entrywise.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 6(c)–(e), p. 15 (Eq. (5), p. 15)

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 6(c)–(e)** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 15). Under Assumptions 1, 2
and 3, for the chain `(i_t)_{t ∈ ℤ}` in steady state and `z_t = Σ_{τ ≤ t} (αλ)^{t−τ} φ(i_τ)`
(Eq. (5)), with `λ ∈ [0, 1]`:
(c) `E_0[z_tφ′(i_t)] = Σ_m (αλ)^m ΦDP^mΦ′`;
(d) `E_0[z_tφ′(i_{t+1})] = Σ_m (αλ)^m ΦDP^{m+1}Φ′`;
(e) `E_0[z_t g(i_t, i_{t+1})] = Σ_m (αλ)^m ΦDP^m ḡ`;
and each expression is well defined and finite (in particular the series (5) converges almost
surely). -/
theorem lemma_6_cde {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ) {N : ℕ} (σ : S → Fin N → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ) (h3 : Assumption3 P π g φ σ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i) :
    ∀ t : ℤ,
      (∀ᵐ ω ∂μ, Summable (fun τ : ℕ => (α * lam) ^ τ • φ (i (t - τ) ω))) ∧
      (∀ k l, Integrable (fun ω => zStat α lam φ i t ω k * φ (i t ω) l) μ) ∧
      HasSum (fun m : ℕ => (α * lam) ^ m • phiDPmPhi P π φ m)
        (fun k l => ∫ ω, zStat α lam φ i t ω k * φ (i t ω) l ∂μ) ∧
      (∀ k l, Integrable (fun ω => zStat α lam φ i t ω k * φ (i (t + 1) ω) l) μ) ∧
      HasSum (fun m : ℕ => (α * lam) ^ m • phiDPmPhi P π φ (m + 1))
        (fun k l => ∫ ω, zStat α lam φ i t ω k * φ (i (t + 1) ω) l ∂μ) ∧
      (∀ k, Integrable (fun ω => zStat α lam φ i t ω k * g (i t ω) (i (t + 1) ω)) μ) ∧
      HasSum (fun m : ℕ => (α * lam) ^ m • phiDPmGbar P π φ g m)
        (fun k => ∫ ω, zStat α lam φ i t ω k * g (i t ω) (i (t + 1) ω) ∂μ) := by sorry

end TDApprox.Conv
