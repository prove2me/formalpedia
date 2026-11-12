-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_ag_parameters
-- name    : QuantumGroupCodes836.Addressability.ag_parameters
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:12:19.451666+00:00
-- url     : https://prove2.me/theorems/9df1e78a-37c0-4592-b98b-695b7b0cac3e
-- title:
--   Proposition 2.11 — AG code and dual parameters
-- statement:
--   Let $F/k$ have full finite constants and genus $g$. Let $P$ sum $n$ distinct rational places, disjoint from $D$, with $2g-2<\deg D<n$. For the actual evaluation code and its Euclidean dual,
--
--   $$k_C=\deg D+1-g,\qquad d(C_L(P,D))\ge n-\deg D,\qquad d(C_L(P,D)^\perp)\ge\deg D-2g+2.$$
--
--   Both distance inequalities mean bounds on every nonzero word, including the infinite empty minimum. These are designed lower bounds, not equalities for realized distance.
--
--   Differences from the source:
--   - encoding: function fields, places, divisors and differentials → finite extensions with full constants, valuation-ring places, finitely supported divisors and Kähler differentials; reason: no separating chart, lifting existence or parameter bound is assumed; regular differential dimension computes genus
--   - encoding: finite coordinate sets and Hamming minima → zero-based finite types, actual submodules and extended-natural minima; reason: relabeling changes no code; the zero code has infinite distance
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Proposition 2.11, p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Lifting

set_option autoImplicit false

namespace QuantumGroupCodes836.Addressability

theorem ag_parameters {k : Type} [Field k] [Fintype k] (F : FunctionFieldData k)
    (P : EvaluationData F) (D : Divisors F)
    (hdisjoint : ∀ i, D (P.places i) = 0)
    (hlow : 2 * (genus F : ℤ) - 2 < AlgebraicCurve.Divisor.degree D)
    (hhigh : AlgebraicCurve.Divisor.degree D < P.n) :
    (Module.finrank k (agCode P D) : ℤ) = AlgebraicCurve.Divisor.degree D + 1 - genus F ∧
    ClassicalDistanceBound (agCode P D) ((P.n : ℤ) - AlgebraicCurve.Divisor.degree D) ∧
    ClassicalDistanceBound (dual (agCode P D)) (AlgebraicCurve.Divisor.degree D - 2 * genus F + 2) := by sorry

end QuantumGroupCodes836.Addressability
