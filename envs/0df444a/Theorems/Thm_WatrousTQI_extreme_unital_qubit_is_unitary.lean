-- Prove2me | Theorems.Thm_WatrousTQI_extreme_unital_qubit_is_unitary
-- name    : WatrousTQI.extreme_unital_qubit_is_unitary
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-11T22:57:49.24482+00:00
-- url     : https://prove2.me/theorems/d3a472c2-ab0c-4858-be8e-237eddefdd23
-- title:
--   Theorem 4.23 proof — extreme unital qubit channels are unitary
-- statement:
--   Every extreme point $\Phi$ of the real convex set of unital quantum channels on a qubit is conjugation by a single unitary matrix: one unitary $U$ satisfies $\Phi(X)=UXU^\dagger$ for every complex $2\times2$ matrix $X$. Membership in the extreme-point set includes membership in the channel set, so complete positivity, trace preservation, and unitality are part of the hypothesis, not omitted assumptions.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Proof of Theorem 4.23, printed pp.227–228 (PDF pp.235–236), reduction to extreme points and the two Kraus-rank cases.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WatrousTQI_UnitalChannels
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

theorem extreme_unital_qubit_is_unitary
    (Φ : QAlgorithms.Superop (Fin 2) (Fin 2))
    (h : Φ ∈ (unitalChannels 2).extremePoints ℝ) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        Φ X = (U : Matrix (Fin 2) (Fin 2) ℂ) * X *
          (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by sorry

end WatrousTQI
