-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_z_rotation_worst_case_lower_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P21.z_rotation_worst_case_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:41:44.034997+00:00
-- url     : https://prove2.me/theorems/be0dc375-52f6-4c34-8719-5da57cc8e58d
-- title:
--   Sharp worst-case slope-four z-rotation lower bound
-- statement:
--   For every real $\varepsilon>0$, there is a real angle $\theta$ such that every finite one-qubit Clifford+T gate word $c$ satisfies
--
--   $$
--   \|U_c-R_z(\theta)\|_{\mathrm{op}}\le\varepsilon
--   \quad\Longrightarrow\quad T(c)\ge-9+4\log_2(1/\varepsilon).
--   $$
--
--   Here $R_z(\theta)=\operatorname{diag}(e^{-i\theta/2},e^{i\theta/2})$, $U_c$ is the chronological matrix product, and $T(c)$ counts actual T instructions from the discrete gate set $H,S,T,\omega I$, where $\omega=e^{i\pi/4}$. No ancillas or measurements are allowed, and no overall phase is removed. The angle can depend on $\varepsilon$ and precedes the universal word quantifier. All positive accuracies are included; for $\varepsilon\ge1/2$ the displayed lower bound is negative. This is the source's explicit worst-case lower bound for z-rotations.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 13, Theorem 30: sharp worst-case slope-4 z lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Theorem 30, PDF pp.13-14: worst-case z-rotation lower bound, including every epsilon > 0.
The hard angle can depend on epsilon; all discrete-phase Clifford+T words are tested. -/
theorem z_rotation_worst_case_lower_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ theta : ℝ, ∀ c : List Letter,
      QAlgorithms.specNorm (wordMatrix c - zRotation theta) ≤ eps →
        -9 + 4 * Real.logb 2 (1 / eps) ≤ (tCount c : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
