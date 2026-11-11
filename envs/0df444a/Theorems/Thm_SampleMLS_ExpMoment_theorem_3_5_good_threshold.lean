-- Prove2me | Theorems.Thm_SampleMLS_ExpMoment_theorem_3_5_good_threshold
-- name    : SampleMLS.ExpMoment.theorem_3_5_good_threshold
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:51:36.206366+00:00
-- url     : https://prove2.me/theorems/825b681d-3de1-4497-a6c6-9f72a4b429bf
-- title:
--   Theorem 3.5(iii), proof — a good threshold below the cap: some θ ≤ Θ has q_θ/C(n,t) ≥ 2^{θ−ψn}/(4Γ(Θ+1))
-- statement:
--   Let $U$ be a finite universe with $n=|U|$, $S\subseteq U$ with $k=|S|$, and $g$ a real function on subsets with $g(X)\ge0$ for $X\subseteq U$, $|X|\le k$. Let $\psi\ge0$, $\Gamma\ge1$, and let the integer cap $\Theta$ satisfy the cap part of (2): $\Theta\ge0$ and $x+1\le\Theta\le x+3$, $x=\psi n+\log_2\Gamma$. If $0\le t\le k$ and $\mu_t(S)\ge\binom{n}{t}2^{-\psi n}/\Gamma$, then
--   $$2^{-\Theta}\le\frac{2^{-\psi n}}{2\Gamma}\le\frac{\mu_t(S)}{2\binom{n}{t}},$$
--   and some integer $\theta\in\{0,\dots,\Theta\}$ satisfies
--   $$\frac{q_\theta}{\binom{n}{t}}\ge\frac{2^\theta\mu_t(S)}{4(\Theta+1)\binom{n}{t}}\ge\frac{2^{\theta-\psi n}}{4\Gamma(\Theta+1)},$$
--   where $q_\theta$ is the number of $X\in\binom{S}{t}$ with $g(X)\le\theta$.
--
--   Differences from the source:
--   - generalization: a solution S ∈ F_I with |S| = k → any S ⊆ U, with k := |S|; reason: the step never uses S ∈ F_I; it specializes to the source by taking S ∈ F_I ⊆ 2^{U_I}
--   - encoding: g(I, X, k) with I and k fixed, a running-time exponent (g ≥ 0) → gk : Finset ℕ → ℝ with 0 ≤ gk X for X ⊆ U, |X| ≤ k; reason: the page writes g(X) = g(I, X, k) once I and k are fixed
--   - reading: X uniform in (U_I choose t), ξ = g(I,X,k) if X ⊆ S and ∞ otherwise; E[2^{−ξ}] = µ_t(S)/C(n,t) > 0; p := q_θ/C(n,t) = Pr[ξ ≤ θ] → the conclusion stated for q_θ/C(n,t) directly; reason: the random variable is the proof device that transfers Lemma 3.8; the claimed bounds are about q_θ/C(n,t)
-- source:
--   Gaspers, Monotone Local Search with Sample-Dependent Running Times, arXiv:2611.01774 (sha256 da381dca…), proof of Theorem 3.5(iii), p. 18 (PDF 20)

import Mathlib
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_SampleMLS_ExpMoment_Model
import Definitions.Def_SampleMLS_ExpMoment_SetSystem
import Definitions.Def_SampleMLS_ExpMoment_MLS

set_option autoImplicit false

open scoped ENNReal

namespace SampleMLS.ExpMoment

/-- Proof of Theorem 3.5(iii), p. 18 (PDF 20): if `µ_t(S) ≥ (n choose t) 2^{−ψn}/Γ` for a set
`S ⊆ U` with `|S| = k` and `0 ≤ t ≤ k`, and the cap satisfies (2), then
`2^{−Θ} ≤ 2^{−ψn}/(2Γ) ≤ µ_t(S)/(2 (n choose t))` and some `θ ∈ {0, …, Θ}` has
`q_θ/(n choose t) ≥ 2^θ µ_t(S)/(4(Θ + 1)(n choose t)) ≥ 2^{θ−ψn}/(4Γ(Θ + 1))`. -/
theorem theorem_3_5_good_threshold (U S : Finset ℕ) (hS : S ⊆ U) (gk : Finset ℕ → ℝ)
    (hg : ∀ X ⊆ U, X.card ≤ S.card → 0 ≤ gk X) (ψ Γ : ℝ) (hψ : 0 ≤ ψ) (hΓ : 1 ≤ Γ) (Θ : ℤ)
    (hΘ : CapOK ψ Γ U.card Θ) (t : ℕ) (ht : t ≤ S.card)
    (hμ : ((U.card.choose t : ℕ) : ℝ) * (2 : ℝ) ^ (-(ψ * (U.card : ℝ))) / Γ ≤ mu gk S t) :
    (2 : ℝ) ^ (-Θ) ≤ (2 : ℝ) ^ (-(ψ * (U.card : ℝ))) / (2 * Γ) ∧
    (2 : ℝ) ^ (-(ψ * (U.card : ℝ))) / (2 * Γ) ≤ mu gk S t / (2 * ((U.card.choose t : ℕ) : ℝ)) ∧
    ∃ θ : ℤ, 0 ≤ θ ∧ θ ≤ Θ ∧
      (2 : ℝ) ^ θ * mu gk S t / (4 * ((Θ : ℝ) + 1) * ((U.card.choose t : ℕ) : ℝ)) ≤
        (qCount gk S t θ : ℝ) / ((U.card.choose t : ℕ) : ℝ) ∧
      (2 : ℝ) ^ ((θ : ℝ) - ψ * (U.card : ℝ)) / (4 * Γ * ((Θ : ℝ) + 1)) ≤
        (qCount gk S t θ : ℝ) / ((U.card.choose t : ℕ) : ℝ) := by sorry

end SampleMLS.ExpMoment
