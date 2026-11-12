-- Prove2me | Theorems.Thm_WatrousTQI_unital_extreme_kraus_criterion
-- name    : WatrousTQI.unital_extreme_kraus_criterion
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-11T22:57:00.58503+00:00
-- url     : https://prove2.me/theorems/0401061a-b2b6-4c8d-aac3-4096df5ef549
-- title:
--   Theorem 4.21 — extremality criterion for unital channels
-- statement:
--   Let $d,m>0$, let $\Phi$ be a trace-preserving completely positive map with $\Phi(I_d)=I_d$, and let $A_0,\ldots,A_{m-1}$ be a complex-linearly independent Kraus family representing $\Phi$ on every operator. Then $\Phi$ is an extreme point of the real convex set of all unital channels if and only if the $m^2$ pairs $(A_b^\dagger A_a,A_aA_b^\dagger)$ are complex-linearly independent. Pairs of matrices encode the block-diagonal operators in equation (4.147) through the natural complex-linear isomorphism; both blocks and the order of their factors are retained.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; Theorem 4.21, equations (4.146)–(4.147), printed p.225 (PDF p.233).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WatrousTQI_UnitalChannels
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

theorem unital_extreme_kraus_criterion (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (Φ : QAlgorithms.Superop (Fin d) (Fin d))
    (hΦ : QAlgorithms.IsChannel Φ)
    (hu : Φ (1 : Matrix (Fin d) (Fin d) ℂ) = 1)
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hLI : LinearIndependent ℂ A)
    (hrep : ∀ X, Φ X = QAlgorithms.krausApply A X) :
    Φ ∈ (unitalChannels d).extremePoints ℝ ↔
      LinearIndependent ℂ (fun ab : Fin m × Fin m =>
        ((A ab.2)ᴴ * A ab.1, A ab.1 * (A ab.2)ᴴ)) := by sorry

end WatrousTQI
