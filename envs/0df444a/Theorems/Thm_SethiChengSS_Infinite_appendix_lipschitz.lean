-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_appendix_lipschitz
-- name    : SethiChengSS.Infinite.appendix_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:09.049999+00:00
-- url     : https://prove2.me/theorems/f8ecbe8a-4306-49d7-ac7d-4055a7c382f0
-- title:
--   Appendix (proof of Theorem 6.1), p. 938 — |v_{n,k}(i, x′) − v_{n,k}(i, x)| ≤ C|x′ − x|/(1 − α), and the same for v_n
-- statement:
--   Under the standing assumptions (2.1)–(2.2) and $0 < \alpha < 1$, the truncated values $v_{n,k}$ of (6.4) and their limit $v_n = \lim_k v_{n,k}$ are Lipschitz in the surplus, with the constant $C$ of (2.2):
--   $$|v_{n,k}(i,x') - v_{n,k}(i,x)| \le \frac{C\,|x'-x|}{1-\alpha}, \qquad |v_n(i,x') - v_n(i,x)| \le \frac{C\,|x'-x|}{1-\alpha}$$
--   for all $n$, $k$, $i$, $x$, $x'$.
--
--   In the paper this bound is what places the limit $v_n$ in $C_1$.
--
--   **Formalization Note.** The values are finite (they are bounded by $w_n$), and the inequalities are stated for their real values. The Lipschitz constant of $f_k(i,\cdot)$ is $C$ because $f_k(i,\cdot)$ is convex, nonnegative and bounded by $C(1+|x|)$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 938, Appendix (proof of Theorem 6.1), the display after "From Assumption (2.2), we have"

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem appendix_lipschitz {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (hα0 : 0 < α)
    (hα1 : α < 1) :
    (∀ n k i x x', |(vTrunc D α n k i x').toReal - (vTrunc D α n k i x).toReal| ≤
      D.C * |x' - x| / (1 - α)) ∧
    (∀ n i x x', |(vLim D α n i x').toReal - (vLim D α n i x).toReal| ≤
      D.C * |x' - x| / (1 - α)) := by sorry

end SethiChengSS.Infinite
