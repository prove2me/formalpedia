-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_distanceAngleObjectives
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.distanceAngleObjectives
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:50:44.838098+00:00
-- url     : https://prove2.me/theorems/599f4e41-3e73-480a-b8ca-63dd13456123
-- title:
--   §III.D: distance and angle objectives (113)–(116)
-- statement:
--   Let $N>0$, let $A,C$ be arbitrary complex $N$ by $N$ matrices, and put $f(U)=\operatorname{Re}\operatorname{tr}(C^\dagger UAU^\dagger)$ for $U\in\mathrm{SU}(N)$. Then
--   $$\|UAU^\dagger-C\|_F^2=\|A\|_F^2+\|C\|_F^2-2f(U).$$
--   A unitary minimizes this distance exactly when it maximizes $f$. If $A,C\ne0$, define the squared cosine between their complex lines by $q(U)=|\operatorname{tr}(C^\dagger UAU^\dagger)|^2/(\|A\|_F^2\|C\|_F^2)$. Maximizers of $q$ are exactly maximizers of the absolute trace. If the trace range is a disk centered at zero, some unitary achieves $f(U)=r_C(A)$, the maximal absolute trace. This last assertion concerns optimal values and does not identify the two optimizer sets.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 21, §III.D: distance and angle objectives (113)–(116)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Distance and angle objectives (113)--(116), PDF p.21.
Printed: the two tasks are equivalent for a circular numerical-range disk.
Changed: the real and absolute overlaps have equal optimal values and a common
optimizer; equality of their optimizer sets is not asserted.
Why: for A=C=E12 in dimension 2 the range is the unit disk, but diag(i,-i)
maximizes the absolute overlap and has real overlap -1 instead of the maximum 1.
The distance identity and nonzero-line angle equivalence are unchanged. -/
theorem distanceAngleObjectives {n : ℕ} (hn : 0 < n) (A C : (Matrix (Fin n) (Fin n) ℂ)) :
    (∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      frobSq ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C) =
        frobSq A + frobSq C - 2 * realTraceOverlap A C U) ∧
    (∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      (∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ,
        frobSq ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C) ≤
          frobSq ((V : (Matrix (Fin n) (Fin n) ℂ)) * A * (V : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C)) ↔
      ∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ, realTraceOverlap A C V ≤ realTraceOverlap A C U) ∧
    (A ≠ 0 → C ≠ 0 → ∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      (∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ, lineCosSq A C V ≤ lineCosSq A C U) ↔
      ∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ,
        ‖Matrix.trace (C.conjTranspose * ((V : (Matrix (Fin n) (Fin n) ℂ)) * A * (V : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖ ≤
        ‖Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖) ∧
    (∀ R : ℝ, 0 ≤ R →
      {z : ℂ | ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        z = Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))} =
        {z : ℂ | ‖z‖ ≤ R} →
      ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        realTraceOverlap A C U = numericalRadius A C) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
