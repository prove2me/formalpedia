-- Prove2me | Theorems.Thm_PackedProduct_isBounded_iff
-- name    : PackedProduct.isBounded_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T14:35:57.745538+00:00
-- url     : https://prove2.me/theorems/dfdb6a58-8a74-45b4-914c-7e48224a4516
-- title:
--   A set in the packed primal-dual space is bounded iff both coordinate projections are
-- statement:
--   The primal-dual space $\mathbb{R}^{n+m}$ on which the proximal method of multipliers runs is formalized as the $\ell^2$ product
--
--   $$
--   \mathrm{PD}(n,m) \;=\; \big(\mathbb{R}^{n} \times \mathbb{R}^{m}\big)_{\ell^2},
--   $$
--
--   so that a pair $(x,p)$ is a single point and the Bregman function $h_x \oplus h_p$ is a single function on it. For a subset $s \subseteq \mathrm{PD}(n,m)$,
--
--   $$
--   s \text{ is bounded} \quad\Longleftrightarrow\quad \pi_1(s) \text{ is bounded and } \pi_2(s) \text{ is bounded},
--   $$
--
--   where $\pi_1, \pi_2$ are the two coordinate projections.
--
--   The equivalence is what lets a statement about the packed iterate $(x^k,p^k)$ be read as a statement about the two sequences separately. That translation is needed in both directions in the analysis of the method of multipliers: the convergence theorem for Bregman proximal methods is applied to the single sequence $(x^k,p^k)$ on $\mathbb{R}^{n+m}$, while its conclusions are stated for $\{x^k\}$ and $\{p^k}$ — for instance, "the packed sequence is unbounded" has to become "$\{x^k\}$ is unbounded or $\{p^k\}$ is unbounded".
--
--   **Formalization Note** The $\ell^2$ product type carries the bornology induced from the plain product along the identity-on-points map, so the statement reduces to the corresponding fact for a product of pseudometric spaces; all of the content is the transfer across the type synonym, which no `simp` set does on its own.
-- source:
--   The coordinate splitting of boundedness used in the proof of Theorem 8 of Eckstein, Nonlinear Proximal Point Algorithms Using Bregman Functions, with Applications to Convex Programming, Math. Oper. Res. 18(1) (1993) 202-226, DOI 10.1287/moor.18.1.202, pp. 220-222, where Theorem 1 is applied on the packed space $\mathbb{R}^{n+m}$ and its unboundedness conclusion has to be returned to the two blocks.

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

namespace PackedProduct

/-- A subset of the packed primal-dual space is bounded exactly when both of its coordinate
projections are. -/
theorem isBounded_iff {n m : ℕ} (s : Set (BregmanPPA.ProxMult.PD n m)) :
    Bornology.IsBounded s ↔
      Bornology.IsBounded ((fun z => (WithLp.ofLp z).1) '' s) ∧
      Bornology.IsBounded ((fun z => (WithLp.ofLp z).2) '' s) := by sorry

end PackedProduct
