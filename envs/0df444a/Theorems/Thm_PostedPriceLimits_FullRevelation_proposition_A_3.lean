-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_proposition_A_3
-- name    : PostedPriceLimits.FullRevelation.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:11.230178+00:00
-- url     : https://prove2.me/theorems/17e747d8-ad14-4759-8873-3ce46fd9f374
-- title:
--   Proposition A.3 — the good event for adaptively posted prices, w.p. $\ge1-\lambda^{-1}$
-- statement:
--   In the construction of §5, for all sufficiently large $n$ and every deterministic mechanism of the analysis model (which knows all $\psi_{t,\gamma},\xi_{t,\gamma}$, visits bidders in order and learns $\pi(j)$, $\tau_t(j)$, $N_{t,j}$ and $Z_{\pi(j),k}$ after each visit), with probability at least $1-\lambda^{-1}$ the event of Proposition A.2 holds and, for all relevant block-visit pairs $(t,i)$, the prices $p\in[0,\infty]^{Z_t}$ posted on $Z_t$ at visit $i$ satisfy:
--   1. for every $\gamma\in\Gamma_{t,i}$ and $A\in\mathcal A_{t,\gamma}$, $\big|U_t(\gamma,A,B_{t,p})-\big(2\mathrm{Avg}[B_{t,p}]+2\mathrm{Avg}[AB_{t,p}]\big)\big|\le2\varepsilon$;
--   2. for every $L\subseteq N_{t,i}\setminus\tau_t(i)$ with $|L|\le n-1$, $\Delta_t(L\cap\tau_t([i-1]),B_{t,p})-\Delta_t(L,B_{t,p})\le2\varepsilon$;
--   3. for every $k,r\in[\kappa]$, $\big|\mathrm{Avg}[B_{t,p}(k,\cdot)\mid Z_{t,r}]-\mathrm{Avg}[B_{t,p}(k,\cdot)\mid Z_{t,r,[i-1]}]\big|\le3\varepsilon$.
--
--   This is the probabilistic core of the full-revelation lower bound: although the prices may depend on all public randomness, they cannot exploit it on the clauses that bidder $i$ actually has.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: π, τ_t, N_{t,i}, ψ_{t,γ}, ξ_{t,γ} and the owner-rank draws sampled as described on printed pp.15–17 → the same objects as deterministic functions of independent Unif[0,1] labels (inversion for ψ, ξ = 2U, coin U < 1/m, rank by cumulative intervals) together with uniform injections τ_t and a uniform permutation π; reason: a coupling with exactly the source's joint law of all objects the statements mention; the mechanism never sees the raw labels
--   - encoding: Pr[event] → Measure.real of the event under the latent law; reason: the event is measurable for measurable mechanisms; same number
--   - encoding: an arbitrary deterministic mechanism (expectations/probabilities over the instance taken implicitly) → a deterministic analysis mechanism whose proposed prices are measurable functions of the randomness (PricesMeasurable); reason: routine measurability that only makes the probability/expectation defined; mechanisms obtained from OFR mechanisms (whose inputs take finitely many values) satisfy it
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition A.3, p.29 (PDF 30); Definition 5.4, p.19 (PDF 20); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis

namespace PostedPriceLimits.FullRevelation

/-- Proposition A.3 (for all sufficiently large `n`). For every deterministic mechanism of the
analysis model, with probability at least `1 − λ^{−1}` the event of Proposition A.2 holds and
the three clauses hold at every relevant block-visit pair with the posted prices. -/
theorem proposition_A_3 : ∃ N : ℕ, ∀ n ≥ N, ∀ M : AnalysisMech n, M.PricesMeasurable →
    1 - (lam n : ℝ)⁻¹ ≤ (latentLaw n).real {ω | GoodEvent M ω} := by sorry

end PostedPriceLimits.FullRevelation
