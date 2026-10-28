-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P44_compact_positive_trace_slices
-- name    : QAlgorithms.Papers.Independent.Support50.P44.compact_positive_trace_slices
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-24T00:03:04.848159+00:00
-- url     : https://prove2.me/theorems/94f5d802-c4bc-426a-a374-854569946d97
-- title:
--   Compact positive trace slices
-- statement:
--   Let $E$ be a finite-dimensional complex Hilbert space and $\alpha\ge0$. Both sets
--
--   $$\{X\ge0:\operatorname{tr}X\le\alpha\},\qquad \{X\ge0:\operatorname{tr}X=\alpha\}$$
--
--   are compact in the finite-dimensional operator topology. Zero-dimensional spaces and $\alpha=0$ are included. These trace constraints provide compact domains for recovery optimization.
-- source:
--   Universal recovery map for approximate Markov chains, arXiv:1504.07251v3, PDF p. 25, Lemma C.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P44

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass compression)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

open QAlgorithms.Papers.Independent.Renew46.P37 (classicalKL)

open Filter

open scoped ENNReal ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A B C E G : Type*}

/-- PDF p.25, Lemma C.1: both positive trace slices, including alpha = 0
and the zero-dimensional space, in the finite matrix topology. -/
theorem compact_positive_trace_slices [Fintype E] [DecidableEq E]
    (alpha : ℝ) (halpha : 0 ≤ alpha) :
    IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} ∧
      IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re = alpha} := by sorry

end QAlgorithms.Papers.Independent.Support50.P44

end
