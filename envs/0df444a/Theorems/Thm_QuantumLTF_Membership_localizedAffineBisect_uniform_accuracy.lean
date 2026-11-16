-- Prove2me | Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_uniform_accuracy
-- name    : QuantumLTF.Membership.localizedAffineBisect_uniform_accuracy
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T19:18:06.033916+00:00
-- url     : https://prove2.me/theorems/a82a88b7-c98a-4bc1-870e-f2813af144b0
-- title:
--   Uniform accuracy and logarithmic depth of localized affine bisection
-- statement:
--   There is a universal constant $C>0$ such that localized affine bisection simultaneously approximates the height function at every point of the dyadic grid to additive error $\eta$, using a depth $q\le C\log(1/\eta)$. The hypotheses are precisely the localization conditions used in Theorem 3.2: $n\ge2$, $0<\epsilon\le1/2$, a unit normal $w$, a reference point satisfying $|\langle w,p\rangle|\ge1/10$, and an initial height estimate within $\epsilon/100$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.2, pp. 23–26 (PDF pp. 24–27), localized bisection accuracy and query-depth analysis.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_error
import Theorems.Thm_QuantumLTF_Membership_local_bisection_parameters

namespace QuantumLTF.Membership

open QAlgorithms

theorem localizedAffineBisect_uniform_accuracy :
    ∃ C : ℝ, 0 < C ∧ ∀ {n b : ℕ}, 2 ≤ n → ∀ ε η : ℝ,
      0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ htil : ℝ),
        ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w p| →
        |htil - height w θ p 0| ≤ ε / 100 →
        ∃ q : ℕ, (q : ℝ) ≤ C * Real.log (1 / η) ∧
          ∀ x : Fin n → Qubits b,
            |(affineBoundaryBisect p (rho n • gridVec n b x) (sgn (inner ℝ w p)) q
                (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) -
              height w θ p (rho n • gridVec n b x)| ≤ η := by sorry

end QuantumLTF.Membership
