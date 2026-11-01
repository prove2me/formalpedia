-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P47_hardy_success_maximum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P47.hardy_success_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:40:05.378786+00:00
-- url     : https://prove2.me/theorems/abf3a4a2-f324-4970-8048-79ff0320a52a
-- title:
--   Attained maximum Hardy success probability
-- statement:
--   Over all normalized noncommuting bases (3), the success probability of the constructed Hardy state is at most $(5\sqrt5-11)/2$. Every allowed parameter choice with $|\alpha_A|=|\alpha_B|=\sqrt{(\sqrt5-1)/2}$ attains that value, and such a parameter choice exists. This is an attained maximum over the two-qubit measurement parameters, without an arbitrary-dimension rigidity assertion.
-- source:
--   Device-independent quantum key distribution based on measurement inputs, arXiv:1308.6447v3, PDF p. 3, II A: optimal Hardy success [21]

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

namespace QAlgorithms.Papers.Independent.Intakethird100.P47

open scoped ComplexConjugate

open scoped BigOperators

/-- II A, PDF p.3, citing [21]: the success probability over all bases (3) has
maximum (5 sqrt(5)-11)/2, attained at the displayed alpha magnitudes. No converse
classification of all optimizers, or arbitrary-dimension self-test, is asserted. -/
theorem hardy_success_maximum :
    (∀ d : HardyParameters,
      hardyBehavior d (pureDensity (psiH d)) false false false false ≤
        (5 * Real.sqrt 5 - 11) / 2) ∧
    (∀ d : HardyParameters,
      (∀ P, ‖d.alpha P‖ = Real.sqrt ((Real.sqrt 5 - 1) / 2)) →
      hardyBehavior d (pureDensity (psiH d)) false false false false =
        (5 * Real.sqrt 5 - 11) / 2) ∧
    (∃ d : HardyParameters,
      (∀ P, ‖d.alpha P‖ = Real.sqrt ((Real.sqrt 5 - 1) / 2)) ∧
      hardyBehavior d (pureDensity (psiH d)) false false false false =
        (5 * Real.sqrt 5 - 11) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P47
