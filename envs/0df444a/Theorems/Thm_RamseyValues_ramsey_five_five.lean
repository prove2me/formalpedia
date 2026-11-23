-- Prove2me | Theorems.Thm_RamseyValues_ramsey_five_five
-- name    : RamseyValues.ramsey_five_five
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T00:18:26.711938+00:00
-- url     : https://prove2.me/theorems/33071179-8851-48e2-a23d-0a110d777af4
-- title:
--   The value of $R(5,5)$ (McKay–Radziszowski–Exoo conjecture)
-- statement:
--   The **Ramsey number** $R(5,5)$ is the least positive integer $n$ such that every red/blue colouring of the edges of the complete graph $K_n$ contains a monochromatic copy of $K_5$; equivalently, every simple graph on $n$ vertices contains a clique of size $5$ or an independent set of size $5$. Its exact value is a well-known open problem: the current bounds are $43 \le R(5,5) \le 46$. From an exhaustive computer enumeration of the $(5,5)$-critical graphs, McKay, Radziszowski and Exoo conjectured that
--   $$R(5,5)=43.$$
--   This conjecture is the goal of the mission; proving it would determine the smallest diagonal Ramsey number whose value is unknown.
--
--   **Formalization Note.** In Lean the statement is `Erdos77.asymmetricRamsey 5 5 = 43`, where `Erdos77.asymmetricRamsey k l` is the platform Ramsey number, defined as the `sInf` of the set of orders forcing a $k$-clique or an $l$-independent set. The Erdős–Szekeres bound makes that set nonempty, so the `sInf` is the genuine minimum and the `sInf ∅ = 0` convention is never reached.
-- source:
--   Conjecture of B. D. McKay, S. P. Radziszowski and G. Exoo. B. D. McKay and S. P. Radziszowski, Subgraph Counting Identities and Ramsey Numbers, J. Combin. Theory Ser. B 69 (1997) 193–209, https://www.sciencedirect.com/science/article/pii/S0095895696917414 ; S. P. Radziszowski, Small Ramsey Numbers, Electron. J. Combin. DS1, https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_five_five : Erdos77.asymmetricRamsey 5 5 = 43 := by sorry

end RamseyValues
