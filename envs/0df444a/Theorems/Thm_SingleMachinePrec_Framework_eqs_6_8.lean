-- Prove2me | Theorems.Thm_SingleMachinePrec_Framework_eqs_6_8
-- name    : SingleMachinePrec.Framework.eqs_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:49:27.430115+00:00
-- url     : https://prove2.me/theorems/414d74fe-b92a-40a0-8067-973f1fc5c958
-- title:
--   Eqs. (6)–(8) — E[w(V_1 ∪ C)] ≤ w(V_1) + (1 − k/t)w(V_{1/2}) ≤ 2(1 − k/t)(w(V_1) + ½w(V_{1/2})) ≤ (2 − 2/(t/k)) OPT
-- statement:
--   Let $S$ be an instance of $1|\mathrm{prec}|\sum w_jC_j$ whose precedence order $P$ is not a linear order, let $L_1,\dots,L_t$ be a $k:t$-realizer of $P$, and let $x$ be a half-integral optimal solution of [CS-LP], with $V_a = \{u : x_u = a\}$. For each $i$ let $C_i = V_1 \cup (V_{1/2} \setminus I_{1/2}(L_i))$, where $I_{1/2}(L_i)$ is the set of pairs of $V_{1/2}$ reversed in $L_i$. Then
--   $$\begin{aligned}
--   \frac1t\sum_{i=1}^t w(C_i) &\le w(V_1) + \Bigl(1-\frac kt\Bigr) w(V_{1/2}) &(6)\\
--   &\le 2\Bigl(1-\frac kt\Bigr)\Bigl(w(V_1) + \frac12 w(V_{1/2})\Bigr) &(7)\\
--   &\le \Bigl(2 - \frac{2}{t/k}\Bigr)\,\mathrm{OPT}, &(8)
--   \end{aligned}$$
--   where $\mathrm{OPT}$ is the minimum weight of a vertex cover of $G^S_P$.
--
--   This chain is the cost estimate of Theorem 5.1. Step (7) uses $t/k \ge 2$, which holds because $P$ is not a linear order; step (8) uses that $w(V_1) + \tfrac12 w(V_{1/2})$ is the optimal value of [CS-LP].
--
--   **Formalization Note** The expectation is the uniform average over the $t$ indices. The paper's assumption $\operatorname{fdim}(P) \ge 2$ is stated as "$P$ is not a linear order" (equivalent by p. 655). $k/t$ and $2/(t/k)$ are real divisions.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 659, Eqs. (6), (7), (8) (proof of Theorem 5.1)

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_CSLP

namespace SingleMachinePrec.Framework

/-- **Eqs. (6)–(8)** (p. 659). Let `P` (the precedence order of `S`) not be a linear order, let
`L_1, …, L_t` be a `k : t`-realizer of `P`, and let `x` be a half-integral optimal solution of
[CS-LP]. With `C_i = V_1 ∪ (V_{1/2} \ I_{1/2}(L_i))`:
(6) `(1/t) ∑_i w(C_i) ≤ w(V_1) + (1 - k/t) w(V_{1/2})`;
(7) `w(V_1) + (1 - k/t) w(V_{1/2}) ≤ 2 (1 - k/t) (w(V_1) + ½ w(V_{1/2}))`;
(8) `2 (1 - k/t) (w(V_1) + ½ w(V_{1/2})) ≤ (2 - 2/(t/k)) · OPT`. -/
theorem eqs_6_8 {N : Type*} [Fintype N] [DecidableEq N] (S : Instance N)
    (hP : ¬ IsLinearOrder N S.P) (k t : ℕ)
    (L : Fin t → LinearExtension S.P) (hL : IsKFoldRealizer S.P k t L)
    (x : IncPair S.P → ℝ) (hx : IsCSLPOptimal S x) (hhalf : IsHalfIntegral x) :
    (1 / (t : ℝ)) * ∑ i, weight S (roundedCover x (L i)) ≤
        weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ∧
      weight S (levelSet x 1) + (1 - (k : ℝ) / t) * weight S (levelSet x (1 / 2)) ≤
        2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ∧
      2 * (1 - (k : ℝ) / t) *
          (weight S (levelSet x 1) + 1 / 2 * weight S (levelSet x (1 / 2))) ≤
        (2 - 2 / ((t : ℝ) / k)) * OPT S := by sorry

end SingleMachinePrec.Framework
