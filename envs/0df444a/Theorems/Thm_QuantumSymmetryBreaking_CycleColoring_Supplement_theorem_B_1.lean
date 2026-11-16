-- Prove2me | Theorems.Thm_QuantumSymmetryBreaking_CycleColoring_Supplement_theorem_B_1
-- name    : QuantumSymmetryBreaking.CycleColoring.Supplement.theorem_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:39.272271+00:00
-- url     : https://prove2.me/theorems/6b359058-beda-4152-82eb-5cd30dfc2c12
-- title:
--   Theorem B.1 — Positivity of the prescribed infinite-dimensional construction
-- statement:
--   For every integer s≥2·10^6, the recursion V_n in equation (2) has a unique Hilbert–Schmidt limit V in ℓ²(G×G), where G is the free product of s involutions. That V and each of the signed projections P_a have bounded-operator realizations on H=ℓ²(G) with exactly their specified coefficients. Set T_a=P_a V P_{−a}, for the 2s signed colors. These actual operators satisfy all three conclusions
--
--   $$T_a^2=0,\qquad \sum_a T_a=|e\rangle\langle e|,\qquad \langle e|T_{a_1}\cdots T_{a_k}|e\rangle\in[0,\infty)$$
--
--   for every color a and every finite word of arbitrary length, including repeated letters and the empty word. The final scalar is explicitly real as well as nonnegative. This companion theorem supplies positivity for the infinite-dimensional construction, with no finite-dimensional or word-length restriction.
--
--   Differences from the source:
--   - encoding: the limit V supplied immediately before B.1 → existence and uniqueness in ℓ²(G×G), then the conclusions for every such limit; reason: avoids a total-function default and pins V to equation (2); no additional hypothesis
--   - encoding: operators on ℓ²(G) and signed colors ±i → continuous linear maps determined by all matrix coefficients, with colors Fin s × Bool; reason: bounded-operator realization preserves the source objects; signed colors stay distinct from group letters
--   - encoding: vacuum products are nonnegative → zero imaginary part and nonnegative real part, for every List including []; reason: complex nonnegativity is rendered literally; foldr uses the source product order
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), Theorem B.1, p.44 (PDF 47)

import Mathlib
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_Supplement_HilbertLimit

set_option autoImplicit false
open scoped ENNReal Topology

namespace QuantumSymmetryBreaking.CycleColoring.Supplement

/-- Theorem B.1, printed pp.44–46 (PDF 47–49). The unique limit is the
Hilbert–Schmidt limit of (2), not an arbitrary solution of the operator identities.
Both signed projections and V have literal bounded-operator realizations. -/
theorem theorem_B_1 (s : ℕ) (hs : 2 * 10 ^ 6 ≤ s) :
    (∃! V : KernelHilbert s, IsSpecifiedLimit V) ∧
    ∀ V : KernelHilbert s, IsSpecifiedLimit V →
      ∃ B : GroupHilbert s →L[ℂ] GroupHilbert s,
      ∃ P : SignedColor s → GroupHilbert s →L[ℂ] GroupHilbert s,
        RealizesKernel (fun p => V p) B ∧
        (∀ a, RealizesKernel (projectionKernel a) (P a)) ∧
        let T := fun a => (P a).comp (B.comp (P (opposite a)))
        (∀ a, (T a).comp (T a) = 0) ∧
        (∑ a, T a) = vacuumProjection s ∧
        (∀ w : List (SignedColor s), (wordVacuum T w).im = 0 ∧
          0 ≤ (wordVacuum T w).re) := by sorry

end QuantumSymmetryBreaking.CycleColoring.Supplement
