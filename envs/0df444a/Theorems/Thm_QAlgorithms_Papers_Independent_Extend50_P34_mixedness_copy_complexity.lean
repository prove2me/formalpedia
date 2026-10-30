-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_mixedness_copy_complexity
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.mixedness_copy_complexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:40:50.05643+00:00
-- url     : https://prove2.me/theorems/ac5117fe-3c73-4666-a76e-550444dfa09e
-- title:
--   Quantum Spectrum Testing: abstract mixedness result / Theorem 1.10
-- statement:
--   For every dimension $d\ge2$ and $0<\epsilon\le1/3$, testing the maximally mixed state against states at trace distance at least $\epsilon$ has copy complexity
--
--   $$\Theta(d/\epsilon^2).$$
--
--   Both constants are absolute, and arbitrary collective measurements on iid copies are allowed with worst-input success probability $2/3$. This is the mixedness result announced in the abstract and stated as Theorem 1.10.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 1, Quantum Spectrum Testing: abstract mixedness result / Theorem 1.10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Quantum Spectrum Testing: abstract mixedness result / Theorem 1.10, arXiv:1501.05028v1, PDF p.1. Domain clarification: the unrestricted-epsilon wording has an empty far promise above 1-1/d. Use the proof-supported uniform regime epsilon≤1/3 and d≥2; PDF pp.6,33-35,43. -/
theorem mixedness_copy_complexity
    : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/3 →
        (∃ n : ℕ, (n : ℝ) ≤ C * d / epsilon^2 ∧
          QuantumTestable d n {unif d} epsilon) ∧
        (∀ n : ℕ, QuantumTestable d n {unif d} epsilon →
          c * d / epsilon^2 ≤ n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
