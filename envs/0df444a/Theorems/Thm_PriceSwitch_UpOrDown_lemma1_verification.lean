-- Prove2me | Theorems.Thm_PriceSwitch_UpOrDown_lemma1_verification
-- name    : PriceSwitch.UpOrDown.lemma1_verification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:04.28099+00:00
-- url     : https://prove2.me/theorems/93e307fd-aec0-42d3-8fbc-e7b433b4eed8
-- title:
--   Lemma 1, p. 1378 — a solution of (3)/(4) above the switch-at-once revenue is the optimal stopping value
-- statement:
--   Let $N$ be a Poisson process with intensity $\lambda_a > 0$ (the demand at the current price $a$), and let $g(m,u)$ be a terminal revenue with $g(0,u) = 0$ and $g(m,\cdot)$ continuous on $[0,\infty)$ for each $m$. Write $J(n,t) = \sup_{\tau \in \mathcal T} E[a\min(n,N(\tau)) + g(n - N(\tau), t - \tau)]$ for the optimal stopping value. Suppose $V(n,t)$, $n \in \mathbb Z_+$, $t \ge 0$, satisfies
--
--   1. $V(0,t) = 0$ and, for $n \ge 1$, $V(n,0) = g(n,0)$ and $V(n,t) \ge g(n,t)$;
--   2. $V(n,\cdot)$ is Lipschitz on every interval $[0,R]$;
--   3. at every $t > 0$ where $V(n,\cdot)$ is differentiable,
--   $$
--   \frac{\partial V(n,t)}{\partial t} = a\lambda_a - \lambda_a\bigl[V(n,t) - V(n-1,t)\bigr] \quad \text{if } V(n,t) > g(n,t), \tag{3}
--   $$
--   $$
--   \frac{\partial V(n,t)}{\partial t} \ge a\lambda_a - \lambda_a\bigl[V(n,t) - V(n-1,t)\bigr] \quad \text{if } V(n,t) = g(n,t). \tag{4}
--   $$
--
--   Then $V(n,t) = J(n,t)$ for all $n$ and all $t \ge 0$.
--
--   This is the verification criterion of the paper. In §5 it is applied with the initial price $p$, intensity $\lambda$, and $g = J(\cdot,\cdot;0) = \max\{J^1(\cdot,\cdot;0), J^2(\cdot,\cdot;0)\}$ ("Lemma 1 applies, with $N(t)$ taking the place of $N_1(t)$", p. 1385); the proof of Theorem 3 ends by checking its conditions.
--
--   **Formalization Note** Lemma 1 as printed is false: with $n = 1$, $V(0,\cdot) = 0$ and $V(1,t) = p_1 + (c - p_1)e^{-\lambda_1 t}$, $c \ge p_1$, in case (i), (3) holds, (4) is vacuous, and yet $J(1,t) < p_1$. The statement adds the four conditions the page's proof uses: $V(n,0) = g(n,0)$ (the proof stops at $\sigma = t$), $V(0,\cdot) = g(0,\cdot) = 0$ (stock runs out; "$J(n,t;0) \doteq 0$ for $n \le 0$"), $V \ge g$ (used in the proof's last step and stated on p. 1379), and local Lipschitz continuity in place of "continuous and almost everywhere differentiable", which does not give the fundamental theorem of calculus that the Brémaud decomposition needs. The terminal function $g$ replaces $J(\cdot,\cdot;0)$, as the page allows (p. 1379); only its continuity is assumed. The rate enters through `IsExpInterarrivals P la T`; `IsProbabilityMeasure P` is redundant given it and is stated for convenience.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 1, p. 1378; applied in §5, p. 1385

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.UpOrDown

open MeasureTheory QueueingFundamentals.Foundations

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Feng–Gallego (1995), Lemma 1, p. 1378, with the boundary, zero-stock, obstacle and
absolute-continuity conditions used by its proof made explicit. -/
theorem lemma1_verification
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ → Ω → ℝ) (a la : ℝ) (hla : 0 < la)
    (hT : IsExpInterarrivals P la T)
    (g : ℕ → ℝ → ℝ) (hg0 : ∀ u, 0 ≤ u → g 0 u = 0) (hgc : ∀ m, ContinuousOn (g m) (Set.Ici 0))
    (V : ℕ → ℝ → ℝ)
    (hV0 : ∀ u, 0 ≤ u → V 0 u = 0)
    (hVinit : ∀ n, 1 ≤ n → V n 0 = g n 0)
    (hVge : ∀ n, 1 ≤ n → ∀ u, 0 ≤ u → g n u ≤ V n u)
    (hVlip : ∀ n, 1 ≤ n → ∀ R : ℝ, ∃ K, LipschitzOnWith K (V n) (Set.Icc 0 R))
    (h3 : ∀ n, 1 ≤ n → ∀ u, 0 < u → g n u < V n u → ∀ d, HasDerivAt (V n) d u →
      d = a * la - la * (V n u - V (n - 1) u))
    (h4 : ∀ n, 1 ≤ n → ∀ u, 0 < u → V n u = g n u → ∀ d, HasDerivAt (V n) d u →
      a * la - la * (V n u - V (n - 1) u) ≤ d) :
    ∀ n t, 0 ≤ t → V n t = PriceSwitch.Markdown.stopValue P T a g n t := by sorry

end PriceSwitch.UpOrDown
