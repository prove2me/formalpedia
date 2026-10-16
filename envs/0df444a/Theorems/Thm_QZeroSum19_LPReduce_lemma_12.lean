-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_lemma_12
-- name    : QZeroSum19.LPReduce.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:02.232356+00:00
-- url     : https://prove2.me/theorems/8e045334-8eb7-49ba-b13f-95229ec6bcef
-- title:
--   Lemma 12, p. 14 — λ* of the game (6) known to error ε‴ = ε/(6R(r+1)) decides OPT < α or OPT ≥ α − ε (added |α| ≤ R; (6) row 2 corrected)
-- statement:
--   Consider the linear program (4), $\max\{b^{\mathsf T}y : Ay \le c,\ y \ge 0\}$ with $A \in \mathbb R^{n\times m}$, and its dual (5), $\min\{c^{\mathsf T}x : A^{\mathsf T}x \ge b,\ x \ge 0\}$, under the standing assumptions of §4: all entries of $A$, $b$, $c$ lie in $[-1,1]$; $R > 0$ and $|c_i| \le R$ for all $i$; the common optimal value $\mathrm{OPT}$ of (4) and (5) is attained by a primal feasible $y$ with $\sum_j y_j \le R$ and by a dual feasible $x$ with $\sum_i x_i \le r$. Let $\alpha \in \mathbb R$ with $|\alpha| \le R$, let $\varepsilon > 0$, and put
--   $$\varepsilon''' = \frac{\varepsilon}{6R(r+1)} .$$
--   Let $\lambda^*$ be the value of the zero-sum game with matrix
--   $$A''' = \begin{pmatrix} e^{\mathsf T} & 1 & -1 \\ -e^{\mathsf T} & -1 & 1 \\ -b^{\mathsf T} & 0 & \alpha/R \\ A & 0 & -c/R \end{pmatrix}, \qquad\qquad (6)$$
--   that is, $\lambda^* = \min_{y''' \in \Delta^{m+2}} \max_k (A'''y''')_k$. If $\tilde\lambda$ is any number with $|\tilde\lambda - \lambda^*| \le \varepsilon'''$, then
--   $$\tilde\lambda > \varepsilon''' \implies \mathrm{OPT} < \alpha, \qquad\qquad \tilde\lambda \le \varepsilon''' \implies \mathrm{OPT} \ge \alpha - \varepsilon .$$
--
--   In the words of the paper: finding the optimal value $\lambda^*$ of the game (6) up to additive error $\varepsilon'''$ suffices to correctly conclude either $\mathrm{OPT} < \alpha$ or $\mathrm{OPT} \ge \alpha - \varepsilon$. Combined with a binary search over $\alpha \in [-R, R]$ and an approximate game solver, it turns any algorithm for zero-sum games into an algorithm for linear programming; Theorem 13 of the paper is obtained this way.
--
--   **Formalization Note** Two deviations from the page, both disclosed. (i) The second row of (6) is printed as $(-e^{\mathsf T}, 1, 1)$; the derivation on p. 13 gives $(-e^{\mathsf T}, -1, 1)$, which is used. With the printed row the lemma is false (for $n = m = 1$, $A = 1$, $c = 1$, $b = -1$, $R = 1$, $r = 0$, $\alpha = 0$ one has $\mathrm{OPT} = 0 \ge \alpha$ but $\lambda^* > 0$). (ii) The hypothesis $|\alpha| \le R$ is added; the proof's step (7) needs it, and §4 supplies it through the binary search over $-R \le \mathrm{OPT} \le R$ and the requirement that (6) have entries in $[-1,1]$. The decision rule ($\tilde\lambda > \varepsilon'''$ versus $\tilde\lambda \le \varepsilon'''$) is the one of the first paragraph of the proof, which reduces to the cases $\lambda^* > 0$ and $\lambda^* \le 2\varepsilon'''$. The value $\lambda^*$ is the infimum of the image of the simplex, not an infimum over a membership condition.
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, Lemma 12 (with (6) on p. 14 and the setting of §4, p. 12)

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem lemma_12 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT α ε : ℝ) (hLP : LPStanding A b c R r OPT) (hα : |α| ≤ R) (hε : 0 < ε)
    (lam : ℝ) (hlam : |lam - QZeroSum19.GK.gameValue (gameMatrix A b c α R)| ≤ epsGame ε R r) :
    (epsGame ε R r < lam → OPT < α) ∧ (lam ≤ epsGame ε R r → α - ε ≤ OPT) := by sorry
end QZeroSum19.LPReduce
