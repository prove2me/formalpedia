-- Prove2me | Theorems.Thm_QAlgorithms_Childs_su2_balanced_lie_bracket
-- name    : QAlgorithms.Childs.su2_balanced_lie_bracket
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T20:07:39.740232+00:00
-- url     : https://prove2.me/theorems/35ee9cfd-6d23-4456-b43b-d93e07433823
-- title:
--   Balanced Lie brackets for small SU(2) logarithms
-- statement:
--   Let $S_r=\{U\in SU(2):\|I-U\|\le r\}$, with the spectral norm. There is $\epsilon_0>0$ such that, whenever $0<\epsilon\le\epsilon_0$ and $A\in S_{\epsilon^2}$, there are complex $2\times2$ matrices $X,Y$ with
--
--   $$\|X\|,\|Y\|\le\tfrac34\epsilon,\qquad e^X,e^Y\in SU(2),\qquad A=e^{XY-YX}.$$
--
--   This is the exact Lie-algebra representation underlying the balanced small-commutator construction. It separates the finite-dimensional geometry of $SU(2)$ from the analytic error in replacing the exponential of a Lie bracket by a group commutator. The fixed factor $3/4$ provides slack for controlling the distances of the exponential factors from the identity.
-- source:
--   Andrew M. Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, §2.4 printed p.9 (PDF page17), proof of Lemma2.3: shortest Pauli logarithm and facts(i),(iii), and the perpendicular equal-length cross-product construction before (2.10). The fixed3/4 slack follows from fact(i) and 1/sqrt(2)<3/4. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Circuit
set_option autoImplicit false

theorem QAlgorithms.Childs.su2_balanced_lie_bracket :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ A ∈ QAlgorithms.su2Ball (ε ^ 2),
        ∃ X Y : Matrix (Fin 2) (Fin 2) ℂ,
          QAlgorithms.specNorm X ≤ (3 / 4 : ℝ) * ε ∧
          QAlgorithms.specNorm Y ≤ (3 / 4 : ℝ) * ε ∧
          NormedSpace.exp X ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
          NormedSpace.exp Y ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
          (A : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (X * Y - Y * X) := by sorry
