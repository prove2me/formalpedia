-- Prove2me | Theorems.Thm_TeschlODE_Stability_complete_of_semiOrbit_subset_compact
-- name    : TeschlODE.Stability.complete_of_semiOrbit_subset_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T13:20:27.202406+00:00
-- url     : https://prove2.me/theorems/b2723952-7cc4-4753-9ad1-a0a994dc9735
-- title:
--   Lemma 6.3 — a forward (backward) orbit in a compact subset of $M$ forces + (−) completeness
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ be open, $f \in C^1(M, \mathbb{R}^n)$, and let $\Phi$ be the flow of $\dot x = f(x)$ with maximal intervals $I_x = (T_-(x), T_+(x))$. Let $\sigma \in \{+1, -1\}$, $x \in M$, and suppose the forward ($\sigma = 1$) resp. backward ($\sigma = -1$) orbit $\gamma_\sigma(x)$ lies in a compact subset $C$ of $M$. Then $x$ is $\sigma$ complete:
--   $$T_\sigma(x) = \sigma\infty, \quad\text{i.e.}\quad \sigma s \in I_x \ \text{ for every } s > 0 .$$
--
--   **Formalization Note.** The book's $f \in C^k$, $k \ge 1$ (standing assumption of §6.2) is taken with $k = 1$, the weakest case. The two directions are one statement parametrized by the real sign $\sigma = \pm 1$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 193, Lemma 6.3

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit

namespace TeschlODE.Stability

theorem complete_of_semiOrbit_subset_compact {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : semiOrbit σ I Φ x ⊆ C) :
    ∀ s : ℝ, 0 < s → σ * s ∈ I x := by sorry

end TeschlODE.Stability
