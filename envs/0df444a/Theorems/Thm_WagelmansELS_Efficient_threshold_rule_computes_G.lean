-- Prove2me | Theorems.Thm_WagelmansELS_Efficient_threshold_rule_computes_G
-- name    : WagelmansELS.Efficient.threshold_rule_computes_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:52.293398+00:00
-- url     : https://prove2.me/theorems/e479dfd3-8016-476f-962f-2537e75ff226
-- title:
--   Section 2: the threshold selector minimizes the backward recursion
-- statement:
--   Fix a period $1\le i\le n$ of an economic lot-sizing instance with nonnegative demands, positive final demand, nonnegative setup costs and unrestricted marginal costs. Construct $G$ from Equation (1), $E_i$ from the lower-envelope vertices, and $q(i)$ from the first consecutive-point ratio below $c_i$. Then
--   $$\min_{i<t\le n+1}\{c_i[D(i)-D(t)]+G(t)\}
--   =c_i[D(i)-D(q(i))]+G(q(i)).$$
--   Consequently, the Iterations assign the backward value itself:
--   $$G(i)=\begin{cases}
--   f_i+c_i[D(i)-D(q(i))]+G(q(i)),&d_i>0,\\
--   \min\{G(i+1),f_i+c_i[D(i)-D(q(i))]+G(q(i))\},&d_i=0.
--   \end{cases}$$
--
--   The theorem captures the paper's selected next production period and its cost calculation. The running-time claim is separate.
--
--   **Formalization Note** The Iterations print $d_{1n}$ where $d_{in}$ is required; the term here is $D(i)-D(q(i))=d_{i,q(i)-1}$, as in the preceding display and Table II. At zero demand, the candidate $t=i+1$ omitted by Equation (1)'s inner minimum cannot improve upon skipping setup because $f_i\ge0$.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), pp. S149–S150, Section 2, display after Proposition 2 and Algorithm, Iterations; corrected d_{1n} slip

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule

namespace WagelmansELS.Efficient

/-- Section 2, pp. S149–S150: the ratio threshold selects a minimizing next period,
and the corrected Iterations assignment gives the backward value. -/
theorem threshold_rule_computes_G (P : Instance) (i : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n) :
    (Finset.Ioc i (P.n + 1)).inf' (by simp; omega) (P.score i) =
      P.score i (P.q i) ∧
    P.G i = (if 0 < P.d i then P.f i + P.score i (P.q i)
      else min (P.G (i + 1)) (P.f i + P.score i (P.q i))) := by sorry

end WagelmansELS.Efficient
