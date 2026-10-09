-- Prove2me | Theorems.Thm_SLQSolv_OpenNotClosed_theorem_4_3_hom
-- name    : SLQSolv.OpenNotClosed.theorem_4_3_hom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:26.299979+00:00
-- url     : https://prove2.me/theorems/ae83bc18-8f8a-4879-8fc7-123920a71668
-- title:
--   Theorem 4.3, pp. 2285–2286, for (SLQ)⁰ on [t, T] — closed-loop solvability iff the Riccati equation has a regular solution
-- statement:
--   Assume (H1)–(H2) and let $t\in[0,T)$. Then the homogeneous Problem (SLQ)$^0$ (that is, $b,\sigma,g,q,\rho=0$) is closed-loop solvable on $[t,T]$ if and only if the Riccati equation (4.6) admits a regular solution on $[t,T]$:
--
--   $$
--   \text{(SLQ)}^0\ \text{closed-loop solvable on }[t,T]\iff \exists\,P\in C([t,T];\mathbb S^n)\ \text{regular solution of (4.6) on }[t,T].
--   $$
--
--   This is Theorem 4.3 of the paper (proved in [23], Sun and Yong 2014) in the case of zero inhomogeneous terms: then the adapted solution of the BSDE (4.11) is $(0,0)$ and condition (4.12) holds automatically (p. 2286). It is the bridge from the non-regularity of the Riccati solution to the failure of closed-loop solvability in Example 7.1.
--
--   **Formalization Note** The paper states Theorem 4.3 on $[0,T]$; Example 7.1 applies it on $[t,1]$, which is the same theorem for the problem restricted to $[t,T]$, so the statement is posed on every $[t,T]$ with $t<T$. Hypotheses (H1)–(H2) are assumed on the full data; Problem (SLQ)$^0$ is the data with the inhomogeneous terms set to zero, and the Riccati equation does not involve those terms. A regular solution on $[t,T]$ is a continuous symmetric solution of (4.6) on $[t,T]$ in integral form with (4.7)–(4.9) on $[t,T]$.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Theorem 4.3 (pp. 2285–2286) and the paragraph after it (p. 2286); applied on [t, 1] in Example 7.1, p. 2305

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Examples

open MeasureTheory Set Filter Topology
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

/-- Theorem 4.3 (pp. 2285–2286, from [23]) for Problem (SLQ)⁰, on `[t, T]`: under (H1)–(H2) the
homogeneous problem is closed-loop solvable on `[t, T]` iff the Riccati equation (4.6) admits a regular
solution on `[t, T]`. -/
theorem theorem_4_3_hom {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω)
    (d : Data Ω n m) (h1 : H1 Bs d) (h2 : H2 Bs d) (t : ℝ≥0) (ht : t < d.T) :
    ClosedLoopSolvableOn Bs d.hom t ↔ ∃ P, IsRegularOn d t P := by sorry

end SLQSolv.OpenNotClosed
