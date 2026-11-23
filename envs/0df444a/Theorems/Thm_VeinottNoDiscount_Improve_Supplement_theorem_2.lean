-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_Supplement_theorem_2
-- name    : VeinottNoDiscount.Improve.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:27:51.736831+00:00
-- url     : https://prove2.me/theorems/35cc944e-1414-4dd5-b64a-f84f60167569
-- title:
--   Theorem 2, p. 1285 — for each β ∈ [0, 1], stationary β-optimal policies that stay α-optimal for α near β on the left, and on the right
-- statement:
--   Consider a finite decision model: finitely many states $s$, finitely many actions, an income $i(s,a)$ and a transition law $q(s'\mid s,a)$. A **policy** $\pi=(f_1,f_2,\dots)$ is a sequence of decision rules $f_n$ (maps from states to actions), and $f^\infty=(f,f,\dots)$ is the **stationary** policy that uses $f$ in every period. For $0\le\beta<1$, $V_\beta(\pi)$ is the vector of expected total $\beta$-discounted incomes of $\pi$ from each initial state. For vectors, $u\ge v$ means $u_s\ge v_s$ for every $s$.
--
--   For $\alpha\in[0,1]$ call a policy $\pi^*$ **$\alpha$-optimal** if
--
--   1. $\alpha<1$ and $V_\alpha(\pi^*)\ge V_\alpha(\pi)$ for every policy $\pi$; or
--   2. $\alpha=1$ and $\pi^*$ is **1-optimal**: $\lim_{\beta\nearrow1}\big[V_\beta(\pi^*)-U(\beta)\big]=0$, where $U(\beta)$ is the value $V_\beta$ of a $\beta$-optimal policy.
--
--   **Theorem 2.** Let $0\le\beta\le1$. Then
--
--   1. there are a decision rule $f$ and $\delta>0$ such that $f^\infty$ is $\alpha$-optimal for every $\alpha$ with
--   $$0\le\alpha\le\beta,\qquad \beta-\delta<\alpha;$$
--   2. there are a decision rule $g$ (possibly different from $f$) and $\delta'>0$ such that $g^\infty$ is $\alpha$-optimal for every $\alpha$ with
--   $$\beta\le\alpha\le1,\qquad \alpha<\beta+\delta'.$$
--
--   Taking $\alpha=\beta$ shows that both $f^\infty$ and $g^\infty$ are $\beta$-optimal. The theorem extends Blackwell's result that some stationary policy is optimal for all discount factors near $1$ to every discount factor $\beta$ in $[0,1]$ and to both sides of it; Example 1 of the paper shows that the two sides may require different stationary policies. Theorem 4 of the paper (1-optimality of stationary policies with lexicographically maximal gain and bias) is derived from the case $\beta=1$.
--
--   **Formalization Note** Every action is available in every state. Optimality is against every policy, including non-stationary ones. 1-optimality is encoded without $U$: for every $\varepsilon>0$, for all $\beta<1$ close enough to $1$, $V_\beta(\pi)\le V_\beta(\pi^*)+\varepsilon$ coordinatewise for every policy $\pi$; this is equivalent to the paper's definition because a $\beta$-optimal policy exists for each $\beta<1$. One $\delta$ serves the whole one-sided neighbourhood and is chosen after the policy.
--
--   Differences from the source:
--
--   - encoding: a finite action set A_s for each state s → one finite action type available in every state; reason: the published model of the base mission; the paper's statements are made in that model throughout this mission
--   - reading: "α-optimal for all α, 0 ≦ α ≦ β (β ≦ α ≦ 1), sufficiently near β" → two conjuncts, each with its own stationary policy and its own δ > 0, for the left and the right one-sided neighbourhood; reason: the parenthesis gives the second case of the statement, and Example 1 (pp. 1285–1286) at β = 1/2 shows that one policy for both sides does not exist in general
--   - encoding: α-optimal at α = 1 means 1-optimal, lim_{β↗1}[V_β(π*) − U(β)] = 0 → the published IsNearlyOptimal (for each ε > 0, V_β(π) ≤ V_β(π*) + ε for all π and all β < 1 near 1); reason: equivalent because a β-optimal policy exists for every β < 1 and U(β) ≥ V_β(π*)
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1285, Theorem 2

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
open Filter Topology BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve.Supplement

/-- **Theorem 2.** For each `0 ≦ β ≦ 1`, there is a β-optimal policy that is stationary and that
is α-optimal for all α, `0 ≦ α ≦ β` (`β ≦ α ≦ 1`), sufficiently near β.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1285, Theorem 2.

**Formalization Note.** "α-optimal" joins the paper's two notions of p. 1285: for `α < 1` it is
β-optimality at discount factor α (`IsBetaOptimal α`, comparison with every policy), and for
`α = 1` it is 1-optimality, the published `IsNearlyOptimal` (Veinott's footnote 2: Blackwell's
"nearly optimal"). The parenthesis is read as a second statement with its own stationary
policy: the first conjunct is the left one-sided neighbourhood `(β − δ, β] ∩ [0, β]`, the second
the right one `[β, β + δ) ∩ [β, 1]`; the case `α = β` lies in both, so each witness is
β-optimal. One `δ > 0` serves the whole neighbourhood and is chosen after the policy. The
model has every action available in every state (`A_s = Act`). -/
theorem theorem_2 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∃ f : St → Act, ∃ δ > (0 : ℝ), ∀ α : ℝ, 0 ≤ α → α ≤ β → β - δ < α →
        (α < 1 → M.IsBetaOptimal α (Policy.stationary f)) ∧
          (α = 1 → M.IsNearlyOptimal (Policy.stationary f))) ∧
      (∃ f : St → Act, ∃ δ > (0 : ℝ), ∀ α : ℝ, β ≤ α → α ≤ 1 → α < β + δ →
        (α < 1 → M.IsBetaOptimal α (Policy.stationary f)) ∧
          (α = 1 → M.IsNearlyOptimal (Policy.stationary f))) := by sorry

end VeinottNoDiscount.Improve.Supplement
