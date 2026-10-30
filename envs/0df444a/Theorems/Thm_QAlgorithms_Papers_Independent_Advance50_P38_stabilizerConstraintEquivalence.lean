-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_stabilizerConstraintEquivalence
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.stabilizerConstraintEquivalence
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:54:18.799034+00:00
-- url     : https://prove2.me/theorems/08c997d7-2e12-4749-9476-a7c07648e199
-- title:
--   §IV.D: trace form of a stabilizer constraint
-- statement:
--   For $N>0$, an arbitrary complex matrix $E\in\mathbb C^{N\times N}$, and $U\in\mathrm U(N)$,
--   $$UEU^\dagger=E\quad\Longleftrightarrow\quad\operatorname{tr}(E^\dagger UEU^\dagger)-\|E\|_F^2=0.$$
--   The trace equation is an equality in $\mathbb C$. It gives an exact stabilizer constraint without asserting real-valuedness of the surrounding penalty objective.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 32, §IV.D: trace form of a stabilizer constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Trace form of the stabilizer constraint, PDF p.32. The equality is
complex-valued; it does not make the printed penalty real-valued. -/
theorem stabilizerConstraintEquivalence {n : ℕ} (hn : 0 < n) (E : (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : (Matrix (Fin n) (Fin n) ℂ)) * E * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose = E ↔
      Matrix.trace (E.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * E * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose)) -
        (frobSq E : ℂ) = 0 := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
