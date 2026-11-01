-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P48_theorem_1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P48.theorem_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:31:11.619854+00:00
-- url     : https://prove2.me/theorems/2044e090-8f6c-447f-babb-527595c48af1
-- title:
--   Every positive weak P_epsilon is strictly parity-distillable
-- statement:
--   For binary inputs and outputs, define $P_\varepsilon$ to assign probability $1/2$ to each equal-output pair and zero to unequal outputs when $xy\ne11$. At $xy=11$, each equal-output pair has probability $(1-\varepsilon)/2$ and each unequal-output pair has probability $\varepsilon/2$. Let $\operatorname{NL}$ be the maximum of the four absolute CHSH expressions, with local bound $2$.
--
--   For every integer $n>1$ and every $0<\varepsilon<1/2$, applying the parallel local-XOR protocol to $n$ independent identical copies gives a valid binary non-signaling output and
--
--   $$
--   \operatorname{NL}\bigl(\operatorname{NDP}_n(P_\varepsilon)\bigr)>\operatorname{NL}(P_\varepsilon)>2.
--   $$
--
--   The protocol uses classical local operations without communication: Alice sends $x$ to each left terminal and XORs her outputs, and Bob does the analogous operation with $y$. This gives strict amplification throughout the stated open parameter interval.
-- source:
--   Distilling Non-Locality, arXiv:0809.3173v4, PDF p. 3, Theorem 1: strict parity distillation of P_epsilon

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P48

namespace QAlgorithms.Papers.Independent.Intakethird100.P48

open scoped BigOperators TensorProduct

noncomputable section

/-- PDF p.3, Theorem 1: for every n>1 and 0<epsilon<1/2 the displayed parity
wiring is a non-locality-distillation protocol in Definition 2's strict sense. -/
theorem theorem_1 (n : ℕ) (epsilon : ℝ)
    (hn : 1 < n) (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2) :
    StrictlyDistills (parityProtocol n) (epsilonBox epsilon) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P48
