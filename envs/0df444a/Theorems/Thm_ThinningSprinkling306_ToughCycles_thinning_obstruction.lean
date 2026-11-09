-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_thinning_obstruction
-- name    : ThinningSprinkling306.ToughCycles.thinning_obstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:06.790109+00:00
-- url     : https://prove2.me/theorems/17e38d02-c636-431e-9482-8283ffe62a19
-- title:
--   Lemma 4.1 — thinning a toughness obstruction
-- statement:
--   Let $G$ be a $t$-tough finite simple graph, let $p\in[0,1]$, and let $\varepsilon>0$ satisfy $\varepsilon p^2t\ge2$. Use the nested conditional-halving law for $V_{p/4}\subseteq V_{p/2}\subseteq V_p$. If
--   $$
--   \Pr(G[V_p]\text{ is not }\varepsilon p^2t\text{-tough})\ge2^{-\varepsilon p^2t},
--   $$
--   then there is a deterministic integer $k\ge2$ such that
--   $$
--   \Pr\big(c_{V_{p/4}}(G[V_{p/2}])\ge k\big)\ge2^{-4k\varepsilon p^2t}.
--   $$
--   Here $c_A$ counts components meeting $A$. The integer is chosen for the distribution, before the sample outcome. This connects failed sampled toughness to a seeded-component event.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: p-random subsets and two conditional independent halvings → Mathlib Bernoulli subset measures and their finite product, with V_p=A, V_{p/2}=A intersect B, V_{p/4}=A intersect B intersect C; reason: A has parameter p and B,C independently have parameter 1/2, so this is exactly the joint thinning law
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 8, Lemma 4.1 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Sprinkling

namespace ThinningSprinkling306.ToughCycles

/-- Lemma 4.1, printed p. 8 (PDF p. 10). -/
theorem thinning_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) (ε p t : ℝ)
    (hε : 0 < ε) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hG : Tough G t)
    (hscale : 2 ≤ ε * p ^ 2 * t)
    (hfail : (2 : ℝ) ^ (-(ε * p ^ 2 * t)) ≤
      sampleProbability p (fun W => ¬ ToughOn G W (ε * p ^ 2 * t))) :
    ∃ k : ℕ, 2 ≤ k ∧
      (2 : ℝ) ^ (-4 * (k : ℝ) * ε * p ^ 2 * t) ≤
        nestedProbability p (fun _ W A => k ≤ (seededComponents G W A).card) := by sorry

end ThinningSprinkling306.ToughCycles
