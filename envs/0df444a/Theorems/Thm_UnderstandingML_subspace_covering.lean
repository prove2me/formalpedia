-- Prove2me | Theorems.Thm_UnderstandingML_subspace_covering
-- name    : UnderstandingML.subspace_covering
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:48:31.592391+00:00
-- url     : https://prove2.me/theorems/8c6c2a20-0f70-46e2-bd90-fa912bf32ae7
-- title:
--   Example 27.1 (as constructed): a set of norm ≤ c in a d-dimensional subspace of ℝ^m has an r-cover of size ≤ (2c√d/r + 1)^d
-- statement:
--   **Example 27.1 (Subspace).** Suppose that $A \subset \mathbb{R}^m$, let $c = \max_{a \in A}\|a\|$, and assume that $A$ lies in a $d$-dimensional subspace of $\mathbb{R}^m$. Then $N(r, A) \le (2c\sqrt d/r)^d$: with an orthonormal basis $v_1, \dots, v_d$ of the subspace and $\epsilon = r/\sqrt d$, the grid $A' = \{\sum_i \alpha'_i v_i : \alpha'_i \in \{-c, -c+\epsilon, \dots, c\}\}$ is an $r$-cover.
--
--   Formally, as the construction gives it: $A$ has an $r$-cover of cardinality at most $(2c\sqrt d/r + 1)^d$; the book's count $(2c/\epsilon)^d$ omits the $+1$ of the grid. The bound $c$ is nonnegative, as the book's $c = \max_{a \in A}\|a\|$ is. For $A = \emptyset$ with $c < 0$ and odd $d$ the right-hand side would be negative.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §27.1 p. 388, Example 27.1 with its construction

import Definitions.Def_UnderstandingML_Covering

open MeasureTheory

namespace UnderstandingML

/-- **Example 27.1 (Subspace)** (p. 388), as its construction gives it. Suppose `A ⊆ ℝ^m`, let
`c = max_{a ∈ A} ‖a‖`, and assume that `A` lies in a `d`-dimensional subspace of `ℝ^m`. Then
`A` has an `r`-cover of size at most `(2c√d/r + 1)^d`, the grid `{∑ᵢ α'ᵢvᵢ : α'ᵢ ∈ {−c, −c+ε, …, c}}`
with `ε = r/√d` in an orthonormal basis `v₁, …, v_d`. (The book writes `(2c√d/r)^d`, the count
`(2c/ε)^d` omitting the `+1` of the grid; the statement here is what the grid gives.) -/
theorem subspace_covering {m d : ℕ} (A : Set (Fin m → ℝ)) (V : Submodule ℝ (Fin m → ℝ))
    (hV : Module.finrank ℝ V = d) (hAV : A ⊆ V) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ a ∈ A, eucNorm a ≤ c) (r : ℝ)
    (hr : 0 < r) :
    ∃ A' : Finset (Fin m → ℝ), IsCover r A A' ∧
      (A'.card : ℝ) ≤ (2 * c * Real.sqrt d / r + 1) ^ d := by sorry

end UnderstandingML
