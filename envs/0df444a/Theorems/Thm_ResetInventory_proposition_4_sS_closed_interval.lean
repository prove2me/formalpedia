-- Prove2me | Theorems.Thm_ResetInventory_proposition_4_sS_closed_interval
-- name    : ResetInventory.proposition_4_sS_closed_interval
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:44.608004+00:00
-- url     : https://prove2.me/theorems/2496df23-d2d4-484e-8cb5-2807944ab8df
-- title:
--   Proposition 4 — the $(s,S)$ lemma on $[0,c_{\max}]$
-- statement:
--   **Proposition 4.** Let $c_{\max}\ge0$ and $K\ge0$, and let $G(\cdot,t)$ be continuous and convex on $[0,c_{\max}]$. Then there exists $S\in[0,c_{\max}]$ such that $G(S,t)\le G(z,t)$ for all $z\in[0,c_{\max}]$. Furthermore, let
--   $$
--   s=\inf\{z\in[0,S]\mid G(S,t)+K=G(z,t)\}.
--   $$
--   If such $s$ exists, then
--
--   1. $G(S,t)+K=G(s,t)$;
--   2. $G(\cdot,t)$ is non-increasing on $[0,s]$;
--   3. $G(S,t)+K\le G(z,t)$ for all $z\in[0,s]$;
--   4. $G(y,t)\le G(z,t)+K$ for all $y,z$ with $s\le y\le z\le c_{\max}$.
--
--   This is the classical $(s,S)$ lemma (Bertsekas, Lemma 4.2.1) for a closed feasible interval. Below $s$, ordering up to $S$ saves more than the fixed cost $K$. From $s$ up to $c_{\max}$, no reachable level saves more than $K$, so nothing is ordered.
--
--   Differences from the source:
--   - generalization: the paper's function G(·,t) = c z + H(z,t) + γ E J((z−w)⁺,t+1) → any function G continuous and convex on [0, c_max]; reason: the proposition's hypotheses are exactly continuity and convexity of G(·,t); the paper's G is an instance
--   - encoding: let s = inf{…}; if such s exists → if the set {z ∈ [0,S] | G S + K = G z} is nonempty, then for s its infimum (sInf); reason: the set is bounded below by 0, so its infimum exists exactly when it is nonempty; the guard avoids Lean's sInf ∅ = 0
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 4, pp.18–19; proof, p.32

import Mathlib

namespace ResetInventory

/-- **Proposition 4** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, pp.18–19. If `G(·, t)`
is continuous and convex on `[0, c_max]`, there exists `S` such that `G(S, t) ≤ G(z, t)` for all
`z ∈ [0, c_max]`. Furthermore, let `s = inf{z ∈ [0, S] | G(S, t) + K = G(z, t)}`. If such `s`
exists, then

1. `G(S, t) + K = G(s, t)`;
2. `G(·, t)` is non-increasing on `[0, s]`;
3. `G(S, t) + K ≤ G(z, t)` for all `z ∈ [0, s]`;
4. `G(y, t) ≤ G(z, t) + K` for all `y, z` with `s ≤ y ≤ z ≤ c_max`.

**Formalization Note** `G` is `G(·, t)` for the fixed `t`, an arbitrary function continuous and
convex on `[0, c_max]`. "`s` exists" is the nonemptiness of the set (it is bounded below by `0`),
and `s` is its `sInf`; nonemptiness is required because Lean's `sInf ∅ = 0`. `c_max ≥ 0`
(Assumption 4) and `K ≥ 0` (Assumption 2) are the paper's standing assumptions. -/
theorem proposition_4_sS_closed_interval (cmax K : ℝ) (G : ℝ → ℝ)
    (hcmax : 0 ≤ cmax) (hK : 0 ≤ K)
    (hcont : ContinuousOn G (Set.Icc 0 cmax)) (hconv : ConvexOn ℝ (Set.Icc 0 cmax) G) :
    ∃ S ∈ Set.Icc 0 cmax, (∀ z ∈ Set.Icc 0 cmax, G S ≤ G z) ∧
      ({z : ℝ | z ∈ Set.Icc 0 S ∧ G S + K = G z}.Nonempty →
        ∀ s : ℝ, s = sInf {z : ℝ | z ∈ Set.Icc 0 S ∧ G S + K = G z} →
          G S + K = G s ∧
          AntitoneOn G (Set.Icc 0 s) ∧
          (∀ z ∈ Set.Icc 0 s, G S + K ≤ G z) ∧
          (∀ y z : ℝ, s ≤ y → y ≤ z → z ≤ cmax → G y ≤ G z + K)) := by sorry

end ResetInventory
