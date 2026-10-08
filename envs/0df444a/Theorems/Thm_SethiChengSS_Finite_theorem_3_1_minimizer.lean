-- Prove2me | Theorems.Thm_SethiChengSS_Finite_theorem_3_1_minimizer
-- name    : SethiChengSS.Finite.theorem_3_1_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:47.637241+00:00
-- url     : https://prove2.me/theorems/0fc8c3ec-09d2-4081-a704-6d7f20f2c134
-- title:
--   Theorem 3.1 (second part), p. 933 — under (4.2), a B_0 feedback rule attains the infimum in (3.2)
-- statement:
--   Consider the Markov-modulated inventory model of Sethi and Cheng under the standing assumptions of §2 and assumption (4.2): for every $n \in \langle 0, N-1\rangle$ and state $i$, $c^i_n x + F_{n+1}(f_{n+1})(i,x) \to +\infty$ as $x \to \infty$.
--
--   Then there is a feedback rule $\hat u_n(i,x)$ with each $\hat u_n$ in the class $B_0$ (nonnegative pointwise limits of nonnegative continuous functions) that attains the infimum in the dynamic programming equation (3.2):
--   $$c_n(i,\hat u_n(i,x)) + F_{n+1}(v_{n+1})(i, x + \hat u_n(i,x)) = \inf_{u \ge 0}\big\{c_n(i,u) + F_{n+1}(v_{n+1})(i,x+u)\big\}$$
--   for every $n \in \langle 0, N-1 \rangle$, every $i$ and every $x$.
--
--   This is the existence half of the paper's optimal feedback policy: the verification theorem (Theorem 3.2) turns any such rule into an optimal policy.
--
--   **Formalization Note** The paper states the existence of the minimizer under the §2 assumptions alone and refers to Beyer, Sethi and Taksar (1998) for the proof. Without a growth condition the infimum need not be attained. Example: $L = N = 1$, $c \equiv 0$, $f_1(x) = \max(-x,0)$, exponential demand; then $\inf_{u\ge 0}\{K\delta(u) + e^{-(x+u)}\}$ is not attained when $e^{-x} > K$. The hypothesis (4.2), which Theorem 4.1 assumes anyway, is therefore added. Because $\hat u_n$ lies in $B_0$, it is nonnegative.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 933, Theorem 3.1 (second sentence); (4.2) from p. 933

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
import Definitions.Def_SethiChengSS_Finite_Model
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SethiChengSS.Finite

/-- Theorem 3.1, second sentence (Sethi–Cheng 1997, p. 933), with (4.2) added (printed gap: the
infimum need not be attained under the §2 assumptions alone): there is a feedback rule
`û_n(i, x)` in `B_0` attaining the infimum in (3.2) for every `n ∈ ⟨0, N − 1⟩`, `i` and `x`. -/
theorem theorem_3_1_minimizer {L : ℕ} (D : Data L) (N : ℕ) (hS : Standing D)
    (h42 : Cond42 D N) :
    ∃ û : ℕ → Fin L → ℝ → ℝ, (∀ n < N, InB0 (û n)) ∧
      ∀ n < N, ∀ i x,
        orderCost D n i (û n i x) + F D n (dpV D N (n + 1)) i (x + û n i x) =
          ⨅ u : {u : ℝ // 0 ≤ u}, (orderCost D n i u + F D n (dpV D N (n + 1)) i (x + u)) := by sorry

end SethiChengSS.Finite
