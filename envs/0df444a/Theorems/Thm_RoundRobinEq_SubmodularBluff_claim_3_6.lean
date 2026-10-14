-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_claim_3_6
-- name    : RoundRobinEq.SubmodularBluff.claim_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:16.141864+00:00
-- url     : https://prove2.me/theorems/e88387ef-686f-4f2f-b3d3-0505ee84e2a2
-- title:
--   Claim 3.6 — under a violated good-wise inequality at round ℓ, both runs allocate the same goods before i's ℓ-th pick, including y_1, …, y_ℓ
-- statement:
--   Let all agents have submodular valuations, $m=kn$, and let $\succ^{\mathrm b}$ be the bluff profile built from an output $h_1,\dots,h_m$ of Algorithm 2. Fix an agent $i$ and an arbitrary ranking $\succ_i$. Let $X=\{x_1,\dots,x_k\}$ be agent $i$'s bundle in Round-Robin$(\boldsymbol\succ^{\mathrm b})$ with $x_j=h_{(j-1)n+i}$, and let $Y=\{y_1,\dots,y_k\}$ be her bundle in Round-Robin$(\succ_i,\boldsymbol\succ^{\mathrm b}_{-i})$, indexed by Algorithm 3. Suppose that for some round $\ell\in[k]$
--   $$v_i(y_\ell\mid X^{\ell-1}_-)>v_i(x_\ell\mid X^{\ell-1}_-).$$
--   Let $B$ and $D$ be the sets of goods allocated, to any agent, before agent $i$ receives a good in round $\ell$, in Round-Robin$(\boldsymbol\succ^{\mathrm b})$ and in Round-Robin$(\succ_i,\boldsymbol\succ^{\mathrm b}_{-i})$ respectively. Then
--   $$B=D\qquad\text{and}\qquad \{y_1,\dots,y_\ell\}\subseteq B.$$
--
--   The claim is the core of the proof of Lemma 3.5, which argues by contradiction: once Lemma 3.5 is known, the hypothesis above never holds. The claim is therefore stated under exactly the contradiction hypothesis of that proof.
--
--   **Formalization Note.** Indices are 0-based: round $\ell$ is `l : Fin k`, agent $i$ is `i : Fin n`, $x_j$ is the entry `h[j*n + i]` of the greedy list, and $X^{\ell-1}_-$ is `prefixSet x l`. $B$ and $D$ are `allocBefore` of the two profiles at step `l*n + i`. The listing $y$ is injective, has image equal to agent $i$'s deviation bundle, and satisfies `IsAlg3Order` relative to $x$. The standing assumptions $m=kn$ (p. 7) and submodularity of all agents (§3.2) are explicit hypotheses; the tie-breaking of Algorithms 2 and 3 is arbitrary.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 12, Claim 3.6 (context and the sets B, D: p. 11, proof of Lemma 3.5)

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff
import Definitions.Def_RoundRobinEq_SubmodularBluff_Alg3

namespace RoundRobinEq.SubmodularBluff

theorem claim_3_6 {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M] (k : ℕ)
    (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i))
    (h : List M) (hh : IsGreedyOrder v h) (i : Fin n) (τ : List M) (hτ : RoundRobinEq.CancelableBluff.IsRanking τ)
    (x : Fin k → M) (hx : ∀ j : Fin k, h[j.val * n + i.val]? = some (x j))
    (y : Fin k → M) (hy_inj : Function.Injective y)
    (hy : Finset.univ.image y = RoundRobinEq.CancelableBluff.roundRobin (Function.update (bluff h) i τ) i)
    (hy3 : IsAlg3Order (v i) x y)
    (l : Fin k)
    (hviol : RoundRobinEq.CancelableBluff.marginal (v i) {x l} (prefixSet x l.val) < RoundRobinEq.CancelableBluff.marginal (v i) {y l} (prefixSet x l.val)) :
    RoundRobinEq.CancelableBluff.allocBefore (bluff h : Fin n → List M) (l.val * n + i.val) =
        RoundRobinEq.CancelableBluff.allocBefore (Function.update (bluff h) i τ) (l.val * n + i.val) ∧
      ∀ j : Fin k, j ≤ l → y j ∈ RoundRobinEq.CancelableBluff.allocBefore (bluff h : Fin n → List M) (l.val * n + i.val) := by sorry

end RoundRobinEq.SubmodularBluff
