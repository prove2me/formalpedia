-- Prove2me | Theorems.Thm_WeldedPath_Supplement_theorem_4_9
-- name    : WeldedPath.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:19:04.155082+00:00
-- url     : https://prove2.me/theorems/c19dc125-99a1-491c-8164-f566bfccceb9
-- title:
--   Theorem 4.9 — $\|(1-\Pi^{\mathrm{good}}_{t+6})\,\mathrm{cpWT}\,\Pi^{\mathrm{good}}_t\|=O(\eta^{\mathrm{step}}_t)$
-- statement:
--   Let $n$ be even, $l\in[2,n-4]$, $N=2^n$, $N_l=2^{n-l}$, $\epsilon_l=2^{-l}$, and fix a valid welded trees instance. Suppose that, for the constant $C_0$ of the section,
--   $$
--   N_l\ge C_0(q+1),\qquad C_0\Bigl((q+1)\epsilon_l+\frac{(n+1)(q+1)^3}{N}\Bigr)\le\frac12 . \tag{49}
--   $$
--   Let $t\le 6q$ and $(\eta^{\mathrm{step}}_t)^2=\epsilon_l+n(t+1)/N$. Then one application of the ordinary compressed welded trees oracle leaves the good space only by
--   $$
--   \bigl\|(1-\Pi^{\mathrm{good}}_{t+6})\cdot\mathrm{cpWT}\cdot\Pi^{\mathrm{good}}_t\bigr\|=O(\eta^{\mathrm{step}}_t).
--   $$
--   Precisely: there are constants $C_0>0$ and $C>0$ such that the operator norm is at most $C\,\eta^{\mathrm{step}}_t$ for every such $n$, $l$, instance, $q$ and $t$ satisfying (49).
--
--   The index rises from $t$ to $t+6$ because cpWT contains six compression operators. Summed over the $q$ queries, this keeps the database close to the good space, from which no crossing can be read.
--
--   **Formalization Note** $\Pi^{\mathrm{good}}_t$ is the projector of `projGood` (boundary $V_{\mathrm{bd}}$), acting as the identity on the query registers; the norm is the operator norm on $X\otimes Y\otimes L\otimes C$.
--
--   Differences from the source:
--   - generalization: one fixed instance G_n with one fixed coloring (pp.14–15) → every valid weld (one bipartite cycle on the leaves) and every proper 3-coloring, with C₀ and C independent of them; reason: the fixed instance is one of them
--   - reading: "for some constant C₀" in (49) and O(η^step_t) → ∃ C₀ > 0 ∃ C > 0, both chosen before n, l, the instance, q and t; reason: (49) fixes C₀ for the whole section and the proofs take it large; the bound is uniform in all parameters
--   - generalization: q ≥ 1 (every algorithm makes at least one query, p.8) → any q ≥ 0; reason: the q ≥ 1 cases are among them
--   - encoding: descriptions (B, H, (u_i, w_i)_i) over abstract forests → abstract vertex set Fin k with each edge stored as (u, v), u < v, labels as indices of Fin M, w_i given as W^fix_{u_i}(ϕ₀) for an assignment ϕ₀; reason: the same canonical good vectors up to renaming, and a w_i not of this form gives |g_D⟩ = 0, so the span is the same
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Theorem 4.9, p.38; (49), p.26; (61), p.32

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood

namespace WeldedPath

namespace Supplement

/-- **Theorem 4.9** (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic
Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…),
Theorem 4.9, p.38). Let `t ≤ 6q` and suppose Eq. (49) holds. Then
`‖(1 − Π^good_{t+6}) · cpWT · Π^good_t‖ = O(η^step_t)`.

Eq. (49) (p.26): for some constant `C₀`, `N_l ≥ C₀(q + 1)` and
`C₀((q + 1)ϵ_l + (n + 1)(q + 1)³/N) ≤ 1/2`, with `N = 2^n`, `N_l = 2^{n−l}`, `ϵ_l = 2^{−l}`;
`(η^step_t)² = ϵ_l + n(t + 1)/N` (61).

**Formalization Note.**
1. `C₀` is the constant of (49), fixed "throughout the rest of the section" (p.26); `O(·)` is one
   absolute constant `C`. Both are chosen before `n`, `l`, the instance, `q` and `t`.
2. The standing assumptions of §3.1 (p.14): `n` even, `l ∈ [2, n − 4]`, any valid weld with a
   proper 3-coloring (`WeldedInstance.IsValid`).
3. `cpWT` is the ordinary compressed welded trees oracle (40) on `X ⊗ Y ⊗ L ⊗ C`;
   `Π^good_t = Π^good_t(V_bd)` is the orthogonal projector onto the span of the canonical good
   vectors with at most `t` records, tensored with the identity on `X ⊗ Y`; the norm is the
   operator norm. -/
theorem theorem_4_9 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ q t : ℕ, t ≤ 6 * q →
      C₀ * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n - l) →
      C₀ * (((q : ℝ) + 1) / (2 : ℝ) ^ l + ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤
        1 / 2 →
      ‖(1 - projGood l G (t + 6)).comp ((cpWT l G).comp (projGood l G t))‖ ≤
        C * etaStep n l t := by sorry

end Supplement

end WeldedPath
