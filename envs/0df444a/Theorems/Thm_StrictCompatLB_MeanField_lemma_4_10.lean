-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_lemma_4_10
-- name    : StrictCompatLB.MeanField.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:41.706746+00:00
-- url     : https://prove2.me/theorems/76789280-249b-4cab-baee-49c8056a3a8e
-- title:
--   Lemma 4.10 — a criterion for tightness in ℓ^ω_1
-- statement:
--   Fix a positive sequence $\omega=(\omega_1,\omega_2,\dots)$ and, for $N\ge N_0$, probability distributions $\pi_N$ on $\mathcal S_N$ (the laws of $\Phi(G_N,\infty)$). Suppose that
--   1. for each fixed $i\ge1$, the laws of $q_i(\Phi(G_N,\infty))$ are tight in $\mathbb R$, and
--   2. for every $\varepsilon>0$,
--   $$\lim_{j\to\infty}\limsup_{N\to\infty}P\Big(\sum_{i=j}^\infty\omega_iq_i(\Phi(G_N,\infty))>\varepsilon\Big)=0 .$$
--   Then the sequence $\{q(\Phi(G_N,\infty))\}$ is tight when $\mathcal Y$ is endowed with the $\ell^\omega_1$-topology.
--
--   It reduces tightness in the weighted space to coordinatewise tightness and a uniform tail estimate.
--
--   **Formalization Note** Tightness in $\ell^\omega_1$ is stated through the isometry $q\mapsto(\omega_iq_i)_{i\ge1}$ onto $\ell_1$ (`IsTightWeighted`). "$\lim_j\limsup_N(\cdot)=0$" is written as: for all $\varepsilon,\eta>0$ there is $j_0$ such that for every $j\ge j_0$ there is $N_1$ with the probability at most $\eta$ for all $N\ge N_1$, which is exact for $[0,1]$-valued quantities. The family is indexed from an arbitrary $N_0$ (the paper's $N_0=1$).
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 21, Lemma 4.10, (4.19); pp. 50–51, App. I

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Lemma 4.10 (p. 21; proof App. I, pp. 50–51). Fix positive weights `ω = (ω_1, ω_2, …)`. Let
`π N` (`N ≥ N₀`) be laws on `S_N`, the laws of `Φ(G_N, ∞)`. If for each `i ≥ 1` the laws of
`q_i(Φ(G_N, ∞))` are tight in `ℝ`, and
`lim_{j→∞} limsup_{N→∞} P(∑_{i ≥ j} ω_i q_i(Φ(G_N, ∞)) > ε) = 0` for every `ε > 0` (4.19),
then the laws of `q(Φ(G_N, ∞))` are tight in `ℓ^ω_1`. -/
theorem lemma_4_10 (ω : ℕ → ℝ) (hω : ∀ i, 1 ≤ i → 0 < ω i) (N₀ : ℕ)
    (π : (N : ℕ) → (Fin N → ℕ) → ℝ) (hπ : ∀ N ≥ N₀, IsProbVec (π N))
    (htight : ∀ i : ℕ, 1 ≤ i → ∀ η : ℝ, 0 < η → ∃ R : ℝ, ∀ N ≥ N₀,
      probOf (π N) {z | R < |occ z i|} ≤ η)
    (h419 : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ N₁ : ℕ, ∀ N ≥ max N₀ N₁,
      probOf (π N) {z | ε < weightedTail ω j z} ≤ η) :
    IsTightWeighted ω N₀ π := by sorry

end StrictCompatLB.MeanField
