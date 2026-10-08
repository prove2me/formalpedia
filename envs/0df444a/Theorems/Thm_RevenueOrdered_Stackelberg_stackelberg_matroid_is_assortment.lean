-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_stackelberg_matroid_is_assortment
-- name    : RevenueOrdered.Stackelberg.stackelberg_matroid_is_assortment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:07.535839+00:00
-- url     : https://prove2.me/theorems/89caa1a7-763c-4b41-8362-8c757251387f
-- title:
--   Theorem 4.16 — Stackelberg Matroid pricing is an assortment problem under a regular choice model, and uniform pricing is revenue-ordered assortments
-- statement:
--   Let $M=(E,\mathcal X)$ be a matroid with a bipartition $E=R\sqcup B$ into red and blue elements ($B\neq\emptyset$), red costs $c:R\to\mathbb R_{>0}$ with distinct values $c_1<\dots<c_k$, and a base of $M$ contained in $R$. Build the assortment instance of the proof: products $\mathcal C=B\times\{c_1,\dots,c_k\}$, revenues $r((e,q))=|B|\,q$, and, for a linear ordering $L$ of $R\cup\mathcal C$ that is non-decreasing in cost with $\mathcal C$ before $R$ on ties,
--   $$
--   \mathcal P((e,q),S)=\begin{cases}1/|B|&\text{if }(e,q)\in\mathrm{greedy}_{M'}(R\cup S,L),\\0&\text{otherwise,}\end{cases}
--   $$
--   where $M'$ is the auxiliary matroid on $R\cup\mathcal C$. Write $\mathrm{rev}_{\mathrm{Stack}}(p,L^*)=\sum_{e\in B\cap\mathrm{greedy}_M(R\cup B,L^*)}p(e)$ for the leader's revenue under prices $p$ when the customer uses a compatible ordering $L^*$. Then:
--
--   1. $\mathcal P$ is a regular discrete choice model and $r>0$;
--   2. the assortment optimum is the optimal Stackelberg revenue:
--   $$
--   \max_{S\subseteq\mathcal C}\sum_{y\in S}\mathcal P(y,S)\,r(y)=\max\bigl\{\mathrm{rev}_{\mathrm{Stack}}(p,L^*): p:B\to\mathbb R_{>0},\ L^*\text{ compatible with }(c,p)\bigr\};
--   $$
--   3. for each red cost level $c_i$ there is $y\in\mathcal C$ such that the revenue-ordered assortment $\{y'\in\mathcal C:r(y')\ge r(y)\}$ earns the revenue of the uniform price $c_i$ on every blue element;
--   4. for each $y\in\mathcal C$ there is a red cost level $c_i$ such that $\{y'\in\mathcal C:r(y')\ge r(y)\}$ earns the revenue of the uniform price $c_i$.
--
--   Through this correspondence the approximation guarantees for revenue-ordered assortments in §3 become guarantees for uniform pricing in Stackelberg Matroid (and Stackelberg Minimum Spanning Tree) pricing, recovering the bounds of Cardinal et al.
--
--   **Formalization Note** The theorem is stated for the explicit instance of the paper's proof (and for every admissible ordering $L$), not as an existence statement. Item 2 is stated with `IsGreatest`: the assortment optimum is an upper bound on every achievable Stackelberg revenue and is achieved by some positive real price assignment, so the Stackelberg optimum is a maximum. Cost levels $c_i$ are quantified as elements of the set of red costs rather than by index. Revenues under a uniform price are asserted for every compatible customer ordering. $B\neq\emptyset$ is needed only for item 3 (otherwise $\mathcal C$ is empty and no $y$ exists).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 24, Theorem 4.16 (proof pp. 32–35)

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

open Classical

namespace RevenueOrdered.Stackelberg

/-- Theorem 4.16 (Berbeglia–Joret, arXiv:1606.01371v3, p. 24), for the explicit assortment
instance of its proof (pp. 32–33): products `𝒞 = B × {c₁, …, c_k}`, revenues
`r((e, q)) = |B| q`, and choice probabilities `𝒫((e, q), S) = 1/|B|` iff
`(e, q) ∈ greedy_{M′}(R ∪ S, L)`. Then (a) the model is regular and `r > 0`; (b) its optimum
`OPT` is the greatest RevenueOrdered.Ratio.revenue achievable in the Stackelberg Matroid instance; (c) for each red cost
level `c_i` some RevenueOrdered.Ratio.revenue-ordered assortment `{y' : r(y') ≥ r(y)}` earns the RevenueOrdered.Ratio.revenue of the uniform
price `c_i`; (d) every RevenueOrdered.Ratio.revenue-ordered assortment earns the RevenueOrdered.Ratio.revenue of some uniform price `c_i`. -/
theorem stackelberg_matroid_is_assortment {α : Type*} (I : Instance α) (hB : I.B.Nonempty)
    (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L) :
    (RevenueOrdered.Ratio.IsRegular (choiceProb I L) ∧ ∀ y : Product I, 0 < prodRevenue I y) ∧
    IsGreatest {v : ℝ | ∃ p : α → ℝ, (∀ e ∈ I.B, 0 < p e) ∧
        ∃ L' : List α, I.IsCustomerOrder p L' ∧ v = I.stackRevenue p L'}
      (RevenueOrdered.Ratio.opt (choiceProb I L) (prodRevenue I)) ∧
    (∀ q ∈ costs I, ∃ y : Product I, ∀ L' : List α, I.IsCustomerOrder (fun _ => q) L' →
        RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) (thresholdSet (prodRevenue I) y) =
          I.stackRevenue (fun _ => q) L') ∧
    (∀ y : Product I, ∃ q ∈ costs I, ∀ L' : List α, I.IsCustomerOrder (fun _ => q) L' →
        RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) (thresholdSet (prodRevenue I) y) =
          I.stackRevenue (fun _ => q) L') := by sorry

end RevenueOrdered.Stackelberg
