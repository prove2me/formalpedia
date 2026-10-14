-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableBluff_domination_ordering
-- name    : RoundRobinEq.CancelableBluff.domination_ordering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:17.647004+00:00
-- url     : https://prove2.me/theorems/69f88397-b6e1-4763-a76b-943f8829a151
-- title:
--   §3.1, proof of Theorem 3.2 — a deviation bundle can be ordered so that its r-th good is worth at most the r-th bluff good
-- statement:
--   Let $m = kn$, let every $v_i$ be a cancelable valuation function, let $\boldsymbol\succ^*$ be a strict variant of the truthful profile, and let $h_1, \dots, h_m$ and $\boldsymbol\succ^{\mathrm b}$ be as in the bluff profile. Under $\boldsymbol\succ^{\mathrm b}$ agent $i$ receives $A_i^{\mathrm b} = \{h_i, h_{n+i}, \dots, h_{(k-1)n+i}\}$. Suppose agent $i$ deviates to any ranking $\succ_i$ and receives $A_i$ in Round-Robin$(\succ_i, \boldsymbol\succ^{\mathrm b}_{-i})$. Then $A_i$ has an ordering $Y^* = (y^*_1, \dots, y^*_k)$ (each good of $A_i$ appearing exactly once) such that
--   $$
--   v_i(\{y^*_r\}) \le v_i(\{h_{(r-1)n+i}\}) \qquad \text{for all } r \in [k].
--   $$
--
--   This is the outcome of the exchange process in the proof of Theorem 3.2; combined with Lemma 3.3 applied to $A_i^{\mathrm b}$ and $A_i$ it gives $v_i(A_i^{\mathrm b}) \ge v_i(A_i)$, which is the theorem.
--
--   **Formalization Note** The ordering is an injective `y : Fin k → M` whose image is agent `i`'s bundle under `Function.update (bluff σ) i τ`. Rounds and agents are 0-based: for `r : Fin k` (the paper's round $r+1$) and agent `i` (the paper's agent $i+1$) the good $h_{rn+i+1}$ is entry `r * n + i` of `pickOrder σ`; the statement asserts that this entry exists. The deviation `τ` ranges over all rankings. The standing $m = kn$ (p. 7) is a hypothesis `hm`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 9, §3.1, proof of Theorem 3.2, last two sentences (ordering Y*)

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.CancelableBluff

theorem domination_ordering {n : ℕ} [NeZero n] {M : Type*} [Fintype M] [DecidableEq M]
    (k : ℕ) (hm : Fintype.card M = k * n) (v : Fin n → Finset M → ℝ)
    (hv : ∀ i, IsValuation (v i)) (hc : ∀ i, IsCancelable (v i))
    (σ : Fin n → List M) (hσ : IsStrictTruthful v σ) (i : Fin n) (τ : List M)
    (hτ : IsRanking τ) :
    ∃ y : Fin k → M, Function.Injective y ∧
      Finset.univ.image y = roundRobin (Function.update (bluff σ) i τ) i ∧
      ∀ r : Fin k, ∃ h : M, (pickOrder σ)[r.val * n + i.val]? = some h ∧
        v i {y r} ≤ v i {h} := by sorry

end RoundRobinEq.CancelableBluff
