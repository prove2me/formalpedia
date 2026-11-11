-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_proposition_A_2
-- name    : PostedPriceLimits.FullRevelation.proposition_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:21.161892+00:00
-- url     : https://prove2.me/theorems/c5bc9347-5bb7-4af3-9802-186a1f7a7423
-- title:
--   Proposition A.2 — rank-set sizes and stability, w.p. $\ge1-\lambda^{-2}$
-- statement:
--   In the construction of §5, for all sufficiently large $n$, with probability at least $1-\lambda^{-2}$ the following hold simultaneously:
--   1. for every block $t\in[n]$ and rank $k\in[\kappa]$, $\big|\mathrm{val}(k)|Z_{t,k}|-|Z_t|\big|\le\varepsilon|Z_t|$;
--   2. for every block $t\in[n]$, rank $k\in[\kappa]$ and bidder set $I\subseteq[n]$, $|Z_{t,k,I}|\ge|Z_t|/\lambda$;
--   3. for every block $t\in[n]$, ranks $k,r\in[\kappa]$, bidder sets $I\subseteq J\subseteq[n]$ and $A\in\mathcal A_{t,\tau_t(I)}$,
--   $$\big|\mathrm{Avg}[A(k,\cdot)\mid Z_{t,r,I}]-\mathrm{Avg}[A(k,\cdot)\mid Z_{t,r,J}]\big|\le\varepsilon.$$
--
--   This event is part of the good event $\mathcal E$; it supplies the nonzero denominators and the rank-mass estimates used in Lemma 5.14 and Proposition 5.10.
--
--   Differences from the source:
--   - encoding: bidders and blocks indexed 1..n; [i−1] = bidders visited before i, [i] = bidders up to i → bidders and blocks are Fin n = {0,…,n−1}; [i−1] ↦ before i = {j | j < i}, [i] ↦ upTo i = {j | j ≤ i}; reason: 0-based indexing of the same objects; no instance changes
--   - encoding: π, τ_t, N_{t,i}, ψ_{t,γ}, ξ_{t,γ} and the owner-rank draws sampled as described on printed pp.15–17 → the same objects as deterministic functions of independent Unif[0,1] labels (inversion for ψ, ξ = 2U, coin U < 1/m, rank by cumulative intervals) together with uniform injections τ_t and a uniform permutation π; reason: a coupling with exactly the source's joint law of all objects the statements mention; the mechanism never sees the raw labels
--   - encoding: Pr[event] → Measure.real of the event under the latent law; reason: the event is measurable for measurable mechanisms; same number
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition A.2, p.28 (PDF 29); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Construction
import Definitions.Def_PostedPriceLimits_FullRevelation_Analysis

namespace PostedPriceLimits.FullRevelation

/-- Proposition A.2 (for all sufficiently large `n`). With probability at least `1 − λ^{−2}`
the three clauses of `EventA2` hold simultaneously. -/
theorem proposition_A_2 : ∃ N : ℕ, ∀ n ≥ N,
    1 - ((lam n : ℝ) ^ 2)⁻¹ ≤ (latentLaw n).real {ω | EventA2 ω} := by sorry

end PostedPriceLimits.FullRevelation
