-- Prove2me | Theorems.Thm_SteinerNav_lemma_6_5
-- name    : SteinerNav.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:54.891414+00:00
-- url     : https://prove2.me/theorems/0ce648f3-e713-4450-9349-864d6d4f6127
-- title:
--   Lemma 6.5 — greedy local minima are $C_\alpha$-approximate, and the return rule outputs a $C_\alpha$-approximate input point
-- statement:
--   Let $\alpha>1$, $C_\alpha=(\alpha+1)/(\alpha-1)$, let $P$ have $n\ge2$ points and let $G=(V,E)$, $V=P\cup R$, be an $\alpha$-navigable graph with Steiner points for $P$. Let $q\in\mathbb R^d$, let $t^*\in P$ be an input point nearest to $q$, and set $r=\|q-t^*\|$.
--
--   1. Every greedy local minimum $x\in V$ satisfies $\|x-q\|\le C_\alpha r$.
--   2. If $G$ has no Steiner-to-Steiner edges, then at every greedy local minimum $x\in V$ the return rule (return $x$ if $x\in P$; return its outgoing neighbor closest to $q$ if $x\in R$) returns something, and every value $y$ it can return lies in $P$ and satisfies
--   $$\|y-q\|\ \le\ C_\alpha\,r .$$
--
--   So greedy search, followed by the return rule, outputs a $C_\alpha$-approximate nearest neighbor in $P$.
--
--   **Formalization Note** "The following rule returns a $C_\alpha$-approximate nearest neighbor in $P$" is stated as: a return value exists, and every return value (every closest out-neighbor, under ties) is in $P$ and within $C_\alpha r$ of $q$.
--
--   Differences from the source: none.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 6.5, p.22; C_α and the standing assumptions of §6.3, p.22

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_GreedyRun

namespace SteinerNav

/-- Lemma 6.5: let `G` be Steiner `α`-navigable, `t*` an input point nearest to `q`, `r = ‖q − t*‖`,
`C_α = (α + 1)/(α − 1)`. Every greedy local minimum `x ∈ V` has `‖x − q‖ ≤ C_α r`. If `G` has no
Steiner-to-Steiner edges, the return rule applies at every local minimum, and each value `y` it can
return is in `P` and a `C_α`-approximate nearest neighbor (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 6.5, p.22). -/
theorem lemma_6_5 {d : ℕ} (α : ℝ) (hα : 1 < α) (P R : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hn : 2 ≤ P.card) (hG : IsSteinerNavigable α P R E) (q tstar : Pt d) (htstar : tstar ∈ P)
    (hnear : ∀ p ∈ P, dist q tstar ≤ dist q p) :
    (∀ x ∈ P ∪ R, GreedyLocalMin E q x → dist x q ≤ (α + 1) / (α - 1) * dist q tstar) ∧
      (NoSteinerToSteiner R P E → ∀ x ∈ P ∪ R, GreedyLocalMin E q x →
        (∃ y, GreedyReturns E P q x y) ∧
          ∀ y, GreedyReturns E P q x y →
            y ∈ P ∧ dist y q ≤ (α + 1) / (α - 1) * dist q tstar) := by sorry

end SteinerNav
