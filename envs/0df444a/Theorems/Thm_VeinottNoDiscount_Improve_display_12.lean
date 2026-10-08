-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_display_12
-- name    : VeinottNoDiscount.Improve.display_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:15.950679+00:00
-- url     : https://prove2.me/theorems/cb5fa9b4-f70f-4777-bf41-d8c0aede0d42
-- title:
--   (12) — z(f) is the unique solution of [I − Q(f)]z = −y(f), Q*(f)z = 0
-- statement:
--   For each decision rule $f\in F$, the system
--   $$[I-Q(f)]\,z=-y(f),\qquad Q^*(f)\,z=0\tag{12}$$
--   has exactly one solution, $z(f)$.
--
--   The vector $z(f)$ is the third coordinate of the triple $(x(f),y(f),z(f))$ that Veinott's extended improvement method increases lexicographically; it plays for the bias the role that the bias plays for the gain.
--
--   **Formalization Note** $z(f)$ is defined as $H(f)(-y(f))$ with $H(f)=(I-Q(f)+Q^*(f))^{-1}-Q^*(f)$; the statement asserts that this vector is the one and only solution of (12).
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, (12)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **(12).** For each `f ε F` let `z(f)` be the unique solution (by Theorem 3) to
(12) `[I − Q(f)]z(f) = −y(f), Q*(f)z(f) = 0`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, (12).

**Formalization Note.** `z M f` is the closed form `H(f)(−y(f))` with Blackwell's deviation
matrix `H(f)`; the statement says it is the one and only solution of (12). -/
theorem display_12 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    ∀ v : St → ℝ, ((1 - M.Q f) *ᵥ v = -(M.y f) ∧ M.Qstar f *ᵥ v = 0) ↔ v = z M f := by sorry

end VeinottNoDiscount.Improve
