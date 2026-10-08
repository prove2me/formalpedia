-- Prove2me | Theorems.Thm_PlunneckeType_Tao_corollary_4_3
-- name    : PlunneckeType.Tao.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:46.188986+00:00
-- url     : https://prove2.me/theorems/9986f67e-74fa-4327-ae3c-e365b9f71bf5
-- title:
--   Corollary 4.3 — |BB| ≤ α|B| and |BAB| ≤ α²|B| give |BA⁻¹AB⁻¹| ≤ α⁶|B|
-- statement:
--   Let $G$ be a group, not necessarily abelian, and let $A$ and $B$ be finite subsets of $G$. Write $XY = \{xy : x \in X,\ y \in Y\}$ for the product set of finite sets $X, Y \subseteq G$, $X^{-1} = \{x^{-1} : x \in X\}$, and $|X|$ for the number of elements of $X$. Let $\alpha$ be a real number and suppose that
--   $$|BB| \le \alpha |B| \qquad \text{and} \qquad |BAB| \le \alpha^2 |B|.$$
--   Then
--   $$|BA^{-1}AB^{-1}| \le \alpha^6 |B|.$$
--
--   No relation between $A$ and $B$ is assumed. The corollary converts a bound on the triple product $BAB$ into a bound on the four-fold product $BA^{-1}AB^{-1}$; it is used in both the proof of Theorem 4.4 and the proof of Theorem 1.6.
--
--   **Formalization Note** Products are taken in the order printed, $B \cdot A^{-1} \cdot A \cdot B^{-1}$; the group is not assumed commutative. Cardinalities are cast to $\mathbb{R}$; there is no sign hypothesis on $\alpha$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 8, Corollary 4.3

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Tao

/-- Petridis, arXiv:1101.3507v3, p. 8, Corollary 4.3. Let `A, B` be finite sets in a (not
necessarily commutative) group with `|BB| ≤ α|B|` and `|BAB| ≤ α²|B|`. Then `|BA⁻¹AB⁻¹| ≤ α⁶|B|`. -/
theorem corollary_4_3 {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hBAB : (#(B * A * B) : ℝ) ≤ α ^ 2 * #B) :
    (#(B * A⁻¹ * A * B⁻¹) : ℝ) ≤ α ^ 6 * #B := by sorry

end PlunneckeType.Tao
