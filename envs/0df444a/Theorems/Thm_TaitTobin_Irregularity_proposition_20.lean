-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_proposition_20
-- name    : TaitTobin.Irregularity.proposition_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:28.288866+00:00
-- url     : https://prove2.me/theorems/b833d3e0-900e-4b85-9167-472d89b5886a
-- title:
--   Proposition 20, p. 18 — partition into a clique U, pendant vertices V and a set W joined only to U
-- statement:
--   There is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ there is $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices maximizing $\lambda_1 - d$, and let $\mathbf v$ be a leading eigenvector with positive entries and maximum entry $1$. Then the vertex set can be partitioned into three sets $U, V, W$ such that
--
--   1. every vertex of $V$ has eigenvector entry smaller than $(2+\varepsilon)/n$ and degree one;
--   2. $U$ induces a clique, every vertex of $U$ has eigenvector entry larger than $1 - 20\varepsilon$, and
--   $$\Bigl(\frac12 - 3\varepsilon\Bigr) n \le |U| \le \Bigl(\frac12 + \varepsilon\Bigr) n ;$$
--   3. every vertex of $W$ has eigenvector entry in $[\tfrac12 - 4\varepsilon, \tfrac12 + 21\varepsilon]$ and is adjacent only to vertices of $U$.
--
--   This is the approximate structure of the extremal graph (Figure 4 of the paper); Theorem 21 then shows $W = \emptyset$ and that all of $V$ hangs from one vertex of $U$.
--
--   **Formalization Note** The page's pendant set $V$ is called `P` in Lean, to avoid a clash with the vertex type. "Partition" is rendered as three pairwise disjoint finite sets whose union is the vertex set (parts may be empty). The proof chooses $\varepsilon$ small (it uses $\varepsilon < 1/50$), hence the quantifier $\exists \varepsilon_0$; $N$ depends on $\varepsilon$. Figure 4's caption also calls $V$ and $W$ independent; that follows from (i) and (iii) and is not part of the proposition.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 18, Proposition 20 (proof pp. 18–20)

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Proposition 20, p. 18: for `ε` small and `n` large, the vertices of a maximizer `G` of `λ₁ − d`
with Perron vector `v` (maximum entry `1`) split into three disjoint sets `U, P, W` (the page's
`U, V, W`) where
(i) every vertex of `P` has entry `< (2 + ε)/n` and degree one;
(ii) `U` is a clique, its entries are `> 1 − 20ε`, and `(1/2 − 3ε)n ≤ |U| ≤ (1/2 + ε)n`;
(iii) every vertex of `W` has entry in `[1/2 − 4ε, 1/2 + 21ε]` and all its neighbours in `U`. -/
theorem proposition_20 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → (∃ x : Fin n, v x = 1) →
      ∃ U P W : Finset (Fin n),
        Disjoint U P ∧ Disjoint U W ∧ Disjoint P W ∧ U ∪ P ∪ W = Finset.univ ∧
        (∀ z ∈ P, v z < (2 + ε) / n ∧ G.degree z = 1) ∧
        (∀ a ∈ U, ∀ b ∈ U, a ≠ b → G.Adj a b) ∧ (∀ z ∈ U, 1 - 20 * ε < v z) ∧
        (1 / 2 - 3 * ε) * (n : ℝ) ≤ (U.card : ℝ) ∧ (U.card : ℝ) ≤ (1 / 2 + ε) * (n : ℝ) ∧
        (∀ z ∈ W, 1 / 2 - 4 * ε ≤ v z ∧ v z ≤ 1 / 2 + 21 * ε) ∧
        (∀ z ∈ W, ∀ y : Fin n, G.Adj z y → y ∈ U) := by sorry
end TaitTobin.Irregularity
