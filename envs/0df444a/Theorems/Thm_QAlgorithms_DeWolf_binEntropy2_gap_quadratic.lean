-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_binEntropy2_gap_quadratic
-- name    : QAlgorithms.DeWolf.binEntropy2_gap_quadratic
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-18T02:47:55.263089+00:00
-- url     : https://prove2.me/theorems/7c3e8225-d82a-4a2b-8aec-b27fb53dec72
-- title:
--   A quadratic lower bound on the binary entropy deficit
-- statement:
--   Let $H_2$ denote binary entropy in bits, with the convention $0\log 0=0$. For every real $\eta\in[0,1/2]$,
--
--   $$1-H_2(1/2+\eta)\ge\eta^2.$$
--
--   This is an explicit lower bound in the quadratic entropy-deficit estimate used to turn a quantum random access code's decoding bias into a qubit lower bound. It includes both endpoints of the interval.
--
--   **Formalization Note** The coefficient is a deliberately weakened absolute constant in the lower half of de Wolf's Eq. (15.3). Entropy in bits is the natural-log binary entropy divided by $\log 2$.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, arXiv:1907.09415v6, PDF p. 143 (printed p. 132), Eq. (15.3) in the proof of Theorem 5; explicit lower half of the quadratic comparison. https://arxiv.org/pdf/1907.09415v6

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false

namespace QAlgorithms.DeWolf

theorem binEntropy2_gap_quadratic (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1 / 2) :
    η ^ 2 ≤ 1 - binEntropy2 (1 / 2 + η) := by sorry

end QAlgorithms.DeWolf
