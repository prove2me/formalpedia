-- Prove2me | Theorems.Thm_ValuativeSYZ_lemma_3_5_biconjugate_le
-- name    : ValuativeSYZ.lemma_3_5_biconjugate_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T11:36:48.81463+00:00
-- url     : https://prove2.me/theorems/0d791b32-48a4-4855-86e7-d66051434e00
-- title:
--   Lemma 3.5 (i): $(\varphi^c)^c \le \varphi$
-- statement:
--   **Lemma 3.5, first part.** For a bounded cost function $c(x,p)$ and a bounded function
--   $\varphi$ on $X$, the double $c$-transform is dominated by the original function:
--   $$(\varphi^{c})^{c} \;\le\; \varphi \qquad \text{pointwise on } X.$$
--   This is the formal half of the statement that the $c$-transform is an order-reversing Galois
--   connection, and it is the first ingredient in identifying the class $P_c$ of the paper as the image
--   of the transform.
--
--   Here $\varphi^{c}(p) = \sup_{x}(c(x,p) - \varphi(x))$ and $\psi^{c}(x) = \sup_{p}(c(x,p) -
--   \psi(p))$. Boundedness of $c$ and of $\varphi$ is what makes the suprema finite; in the paper it
--   comes from the uniform Lipschitz estimate on the skeleton, which is compact.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15, Lemma 3.5 (first assertion)

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

set_option autoImplicit false

open MeasureTheory

namespace ValuativeSYZ

/-- **Lemma 3.5 (first part).** The `c`-transform is order reversing and the double
`c`-transform of a bounded function is dominated by the function itself. -/
theorem lemma_3_5_biconjugate_le {X B : Type*} [Nonempty X] [Nonempty B]
    (c : X → B → ℝ) (φ : X → ℝ) (M : ℝ)
    (hc : ∀ x p, |c x p| ≤ M) (hφ : ∀ x, |φ x| ≤ M) (x : X) :
    ctransformDual c (ctransform c φ) x ≤ φ x := by sorry

end ValuativeSYZ
