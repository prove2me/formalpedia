-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P45_greedyWithinFour
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P45.greedyWithinFour
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:25:40.45694+00:00
-- url     : https://prove2.me/theorems/0839c475-6a4f-4f2e-a463-1ecd0746ff32
-- title:
--   Global shortest-path greedy is within a factor of four
-- statement:
--   Consider a finite square-grid network with distinct terminals $a,b$ in the paper's one-slot heralded-loss model. Each physical edge independently supplies at most one perfect EPR pair with probability $p\in[0,1]$. After seeing all external-success flags, a schedule selects disjoint memory pairs for simultaneous BSMs, whose independent success probability is $q\in[0,1]$. The terminals retain their delivered halves. Let $R_g(p,q)$ be the expected delivered ebits per slot under repeated shortest-path selection and edge deletion, using a fixed shortest-path tie choice. Let $R_{\mathrm{opt}}(p,q)$ be the optimum expected rate over all such one-slot pairwise-BSM schedules that observe external flags but cannot see future BSM outcomes. Then
--
--   $$\frac{R_{\mathrm{opt}}(p,q)}4\le R_g(p,q)\le R_{\mathrm{opt}}(p,q).$$
--
--   The rates are constructed by averaging the conditional path-sum yields over independent external-success subgraphs; disconnected slots contribute zero. This is a restricted-protocol guarantee, rather than a statement about unrestricted quantum-network capacity.
-- source:
--   Routing entanglement in the quantum internet, arXiv:1708.07142v2, PDF p. 5, §II.B.1: global shortest-path greedy routing is within factor four

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P45

namespace QAlgorithms.Papers.Independent.Intakethird100.P45

open scoped BigOperators

noncomputable section

/-- PDF pp.5–7: actual shortest-path greedy achieves at least one quarter
of the actual global optimum, and no more than the optimum. Both rates and
all pairings are constructed above. Disconnected slots contribute zero.
Endpoints `p,q=0,1` are allowed; a direct edge has zero BSMs, even at `q=0`. -/
theorem greedyWithinFour (N : ℕ) (G : GridNetwork N) (a b : Fin N)
    (hab : a ≠ b) (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    optimalGlobalRate G a b p q / 4 ≤ greedyRate G a b p q ∧
    greedyRate G a b p q ≤ optimalGlobalRate G a b p q := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P45
