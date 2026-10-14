-- Prove2me | Theorems.Thm_RoundRobinEq_SubmodularBluff_theorem_3_7
-- name    : RoundRobinEq.SubmodularBluff.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:07.350238+00:00
-- url     : https://prove2.me/theorems/d4387468-61be-44a1-ade5-8d2f87136c72
-- title:
--   Theorem 3.7 — for submodular valuations the bluff profile is a 1/2-approximate PNE of Round-Robin, and 1/2 is tight
-- statement:
--   **Bound.** Let $n\ge1$ agents have submodular valuation functions $v_1,\dots,v_n$ (normalized and non-decreasing) over $m=kn$ goods, and let $\succ^{\mathrm b}$ be an output $h_1\succ^{\mathrm b}\cdots\succ^{\mathrm b}h_m$ of Algorithm 2. Then the bluff profile $\boldsymbol\succ^{\mathrm b}=(\succ^{\mathrm b},\dots,\succ^{\mathrm b})$ is a $\tfrac12$-approximate pure Nash equilibrium of Mechanism 1 (Round-Robin): for every agent $i$ and every ranking $\succ_i$,
--   $$\tfrac12\, v_i\big(\mathcal M(\succ_i,\boldsymbol\succ^{\mathrm b}_{-i})\big)\ \le\ v_i\big(\mathcal M(\boldsymbol\succ^{\mathrm b})\big).$$
--
--   **Tightness.** For every $\varepsilon>0$ there is an instance with submodular valuations (and $m=kn$) in which the bluff profile is not a $(\tfrac12+\varepsilon)$-approximate PNE.
--
--   This is the main result of §3.2: for submodular agents exact equilibria may fail to exist (Proposition 3.4), but the bluff profile is always within a factor $2$ of a best response, and no better factor holds for it in general.
--
--   **Formalization Note.** The bound is stated for every greedy order `h` (`IsGreedyOrder v h`), that is, for every tie-breaking of Algorithm 2; the paper's lexicographic bluff profile is one of them. The standing simplification $m=kn$ (p. 7) is a hypothesis; the paper calls it without loss of generality by adding dummy goods, a reduction this statement does not formalize. In the tightness part the instance is existentially quantified with agents `Fin n` and goods `Fin m`, $m=kn$, and it must admit a greedy order; the conclusion holds for every greedy order of the instance. The paper's instance has $5$ goods for $2$ agents and needs a dummy sixth good to satisfy $m=kn$.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 12, Theorem 3.7 (proof pp. 12–14)

import Mathlib
import Definitions.Def_RoundRobinEq_SubmodularBluff_Setting
import Definitions.Def_RoundRobinEq_SubmodularBluff_Bluff

namespace RoundRobinEq.SubmodularBluff

theorem theorem_3_7 :
    (∀ {n : ℕ} [NeZero n] {M : Type} [Fintype M] [DecidableEq M] (k : ℕ),
      Fintype.card M = k * n →
      ∀ v : Fin n → Finset M → ℝ, (∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i)) →
      ∀ h : List M, IsGreedyOrder v h → RoundRobinEq.CancelableBluff.IsApproxPNE (1 / 2) v (bluff h)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ (n m k : ℕ) (_ : NeZero n) (_ : m = k * n) (v : Fin n → Finset (Fin m) → ℝ),
        (∀ i, RoundRobinEq.CancelableBluff.IsValuation (v i) ∧ IsSubmodular (v i)) ∧
        (∃ h : List (Fin m), IsGreedyOrder v h) ∧
        ∀ h : List (Fin m), IsGreedyOrder v h → ¬ RoundRobinEq.CancelableBluff.IsApproxPNE (1 / 2 + ε) v (bluff h)) := by sorry

end RoundRobinEq.SubmodularBluff
