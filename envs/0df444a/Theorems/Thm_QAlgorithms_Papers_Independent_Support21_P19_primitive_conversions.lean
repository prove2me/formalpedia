-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P19_primitive_conversions
-- name    : QAlgorithms.Papers.Independent.Support21.P19.primitive_conversions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:58:41.46672+00:00
-- url     : https://prove2.me/theorems/e509648f-81f5-478d-ad9e-3d0064a9753b
-- title:
--   Primitive resource conversions
-- statement:
--   Using free local operations and product ancillas, each of the following exact resource simulations is possible, with no supplied EPR pair or additional nonlocal resource:
--
--   $$
--   1\,[q\to q]\ge1\,[q\to qq],\qquad
--   1\,[q\to qq]\ge1\,[c\to c],\qquad
--   1\,[q\to qq]\ge1\,[qq].
--   $$
--
--   The three simulations are separate protocols. The last supplies the local state $|+\rangle$ to the cobit and produces the normalized EPR pair; it does not assert that a general message simultaneously yields a classical bit and an EPR pair. Exact channel simulation retains arbitrary input references.
-- source:
--   Coherent Communication of Classical Messages, arXiv:quant-ph/0307091v3, PDF p. 1, Primitive resource conversions

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P19

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1–2: three separate primitive conversions, with zero borrowed EPR pairs. -/
theorem primitive_conversions :
    Exact (qubitChannel 2) (budget 1 0 0 0 0 0 0 0) (cobitChannel 2) ∧
    Exact (cobitChannel 2) (budget 1 0 0 0 0 0 0 0) (cbitChannel 2) ∧
    Exact (cobitChannel 2) (budget 1 0 0 0 0 0 0 0) (entangled 2) := by sorry

end QAlgorithms.Papers.Independent.Support21.P19

end
