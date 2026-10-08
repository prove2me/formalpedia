-- Prove2me | Theorems.Thm_TalagrandConc_Assignment_lemma_10_1
-- name    : TalagrandConc.Assignment.lemma_10_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:00.805986+00:00
-- url     : https://prove2.me/theorems/24947cb4-5859-4c8b-9738-1885e2787b85
-- title:
--   Lemma 10.1 — in an α-expanding digraph every point lies on a short τ-alternating cycle
-- statement:
--   Let $D \subseteq I \times J$ be an $\alpha$-expanding digraph ($\alpha \ge 2$), where $I$ and $J$ have cardinal $N$, and let $m \ge 1$ be an integer with $\alpha^m \ge N/2$. Let $\tau$ be a one-to-one map from $I$ onto $J$. Then for every $i \in I$ there exist an integer $n$ with $1 \le n \le 2m$ and points $i_1 = i, i_2, \dots, i_n$ of $I$, pairwise distinct, such that, writing $i_{n+1} = i$,
--   $$(i_\ell, \tau(i_{\ell+1})) \in D \qquad \text{for } 1 \le \ell \le n.$$
--
--   The cycle $i_1 \to i_2 \to \dots \to i_{n+1} = i_1$ lets one re-route the assignment $\tau$ along edges of $D$; this is the combinatorial input of Corollary 10.2.
--
--   **Formalization Note** The cycle is a map $c : \mathbb N \to I$ with $c(0) = c(n) = i$, injective on $\{0, \dots, n-1\}$; $c(\ell)$ is the paper's $i_{\ell+1}$. The page prints $(i, \tau(i_{\ell+1}))$, a typo for $(i_\ell, \tau(i_{\ell+1}))$ (the proof uses the latter). The conditions $n \ge 1$ and $m \ge 1$ are implicit in the paper: with $n = 0$ the conclusion would be empty, and with $m = 0$ (possible only for $N \le 2$) it would be false.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 167, Lemma 10.1

import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

namespace TalagrandConc.Assignment

/-- Talagrand (1995), p. 167, Lemma 10.1. For an `α`-expanding digraph `D`, an integer
`m ≥ 1` with `α^m ≥ N/2` and an assignment `τ`, every `i ∈ I` lies on a cycle
`i_1 = i, i_2, …, i_{n+1} = i` with `1 ≤ n ≤ 2m`, `i_1, …, i_n` pairwise distinct and
`(i_ℓ, τ(i_{ℓ+1})) ∈ D` for `1 ≤ ℓ ≤ n`. Indices are 0-based: `c ℓ` is `i_{ℓ+1}`. -/
theorem lemma_10_1 {N : ℕ} (D : Set (Fin N × Fin N)) (α : ℝ) (hD : IsExpanding N α D)
    (m : ℕ) (hm : 1 ≤ m) (hαm : (N : ℝ) / 2 ≤ α ^ m) (τ : Equiv.Perm (Fin N)) (i : Fin N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 * m ∧ ∃ c : ℕ → Fin N, c 0 = i ∧ c n = i ∧
      (∀ a b : ℕ, a < n → b < n → c a = c b → a = b) ∧
      ∀ ℓ : ℕ, ℓ < n → (c ℓ, τ (c (ℓ + 1))) ∈ D := by sorry

end TalagrandConc.Assignment
