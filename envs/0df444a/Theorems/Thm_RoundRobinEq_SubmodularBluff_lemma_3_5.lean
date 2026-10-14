-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_lemma_3_5
-- name    : RoundRobinEq.SubmodularBluff.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:37.83395+00:00
-- url     : https://prove2.me/theorems/ae5a9ef2-3391-44fd-b373-d5501a71376c
-- title:
--   Lemma 3.5 — good-wise marginal domination of the deviation bundle by the bluff bundle
-- statement:
--   Let all agents have submodular valuations, $m=kn$, and let $\succ^{\mathrm b}$ be the bluff profile built from an output $h_1,\dots,h_m$ of Algorithm 2. Fix an agent $i$ and an arbitrary ranking $\succ_i$. Let $X=\{x_1,\dots,x_k\}$ be agent $i$'s bundle in Round-Robin$(\boldsymbol\succ^{\mathrm b})$, indexed in the order the goods were allocated ($x_j=h_{(j-1)n+i}$), and let $Y=\{y_1,\dots,y_k\}$ be her bundle in Round-Robin$(\succ_i,\boldsymbol\succ^{\mathrm b}_{-i})$, indexed by Algorithm 3. Then for every $j\in[k]$,
--   $$v_i(x_j\mid X^{j-1}_-)\ \ge\ v_i(y_j\mid X^{j-1}_-),$$
--   where $X^{j-1}_-=\{x_1,\dots,x_{j-1}\}$.
--
--   The lemma compares the two bundles good by good, which is the input of the per-round inequality in the proof of Theorem 3.7.
--
--   **Formalization Note.** Indices are 0-based (`j : Fin k`); $x_j$ is `h[j*n + i]` and $X^{j-1}_-$ is `prefixSet x j`. The listing $y$ is injective, its image is `roundRobin (Function.update (bluff h) i τ) i`, and it satisfies `IsAlg3Order (v i) x y`. The standing assumptions $m=kn$ and submodularity of all agents are explicit hypotheses; the tie-breaking of Algorithms 2 and 3 is arbitrary, which makes the statement at least as strong as the paper's lexicographic one.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 11, Lemma 3.5

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_Alg3

namespace RoundRobinEq.SubmodularBluff

theorem lemma_3_5 {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M] (k : ℕ)
    (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i))
    (h : List M) (hh : IsGreedyOrder v h) (i : Fin n) (τ : List M) (hτ : RoundRobinEq.CancelableBluff.IsRanking τ)
    (x : Fin k → M) (hx : ∀ j : Fin k, h[j.val * n + i.val]? = some (x j))
    (y : Fin k → M) (hy_inj : Function.Injective y)
    (hy : Finset.univ.image y = RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff h) i τ) i)
    (hy3 : IsAlg3Order (v i) x y) :
    ∀ j : Fin k, RoundRobinEq.CancelableBluff.marginal (v i) {y j} (prefixSet x j.val) ≤ RoundRobinEq.CancelableBluff.marginal (v i) {x j} (prefixSet x j.val) := by sorry

end RoundRobinEq.SubmodularBluff
