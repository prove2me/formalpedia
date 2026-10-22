-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_det_identity
-- name    : TemperleyLieb.Gram.det_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:27.753995+00:00
-- url     : https://prove2.me/theorems/90ec37d4-dd23-40ff-8646-411f26063c34
-- title:
--   §5, p. 19 — determinant as a product of seminormal norms
-- statement:
--   For a shape $\lambda=(f,n-2f)$, the Gram determinant of its cell module in the Murphy basis agrees, after passage from $R=\mathbb Z[x]$ to its fraction field $F$, with the product of seminormal norms:
--
--   $$\det(\lambda)=\prod_{t\in\mathfrak T_n(\lambda)}\langle f_t,f_t\rangle.$$
--
--   The same identity holds for the field-level Gram matrix. This identification makes the determinant in the final formula the determinant of the computed cell form rather than a definition by the desired product.
--
--   **Formalization Note** Integral and fraction-field Murphy data and the specified JM family are asserted to exist. The Gram entry and determinant are those of the published cellular package; $f_t$ is its computed seminormal vector.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 19, §5 opening paragraph, definition of det(lambda)

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08
open scoped BigOperators

/-- Enyang, §5, p. 19: the product of squared seminormal norms is the
Gram determinant of the cell module in the Murphy basis. -/
theorem det_identity (n : ℕ) (hn : 1 ≤ n) :
    (∃ D : RDatum n, IsMurphyDatum R Polynomial.X n D) ∧
    (∃ DF : FDatum n, IsMurphyDatum F xF n DF ∧
      ∃ J : JMFamily DF (n + 1), IsPaperJMFamily n DF J) ∧
    ∀ (D : RDatum n) (DF : FDatum n) (J : JMFamily DF (n + 1)),
      IsMurphyDatum R Polynomial.X n D →
      IsMurphyDatum F xF n DF → IsPaperJMFamily n DF J →
      ∀ f : Fin (n / 2 + 1),
        algebraMap R F (gramDet D f) =
          ∏ t : Tab n f,
            cellForm DF f (seminormalVector J f t) (seminormalVector J f t) ∧
        gramDet DF f =
          ∏ t : Tab n f,
            cellForm DF f (seminormalVector J f t) (seminormalVector J f t) := by sorry

end TemperleyLieb.Gram
