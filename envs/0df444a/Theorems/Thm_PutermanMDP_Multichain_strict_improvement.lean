-- Prove2me | Theorems.Thm_PutermanMDP_Multichain_strict_improvement
-- name    : PutermanMDP.Multichain.strict_improvement
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T03:00:28.050991+00:00
-- url     : https://prove2.me/theorems/846fafc7-2b5d-4ca2-a06d-04070a90b22e
-- title:
--   Proposition 9.2.2 — strict improvement near discount one
-- statement:
--   Let $d,\delta$ be admissible deterministic rules in the finite model. Suppose that whenever $\delta(s)\ne d(s)$, either $P_\delta g^d(s)>P_dg^d(s)$, or $P_\delta g^d(s)=P_dg^d(s)$ and $r_\delta(s)+P_\delta h^d(s)>r_d(s)+P_dh^d(s)$. The printed assertion is
--   $$\exists s\in S,\quad\liminf_{\lambda\uparrow1}\bigl(v_\lambda^{\delta^\infty}(s)-v_\lambda^{d^\infty}(s)\bigr)>0.$$
--   This is the strict discounted improvement assertion used by the termination argument.
--
--   **Formalization Note** The source omits a requirement that any state change. This faithful item preserves that omission and is expected to be disproved: for a one-state zero-reward self-loop and $\delta=d$, its hypotheses hold and its lower limit is zero (finding F2). The lower limit is extended-real, allowing $+\infty$.
-- source:
--   Puterman, Markov Decision Processes: Discrete Stochastic Dynamic Programming, Wiley, 1994, https://doi.org/10.1002/9780470316887, p. 456 (PDF 472), Proposition 9.2.2, (9.2.12)–(9.2.14)

import Mathlib
import Definitions.Def_PutermanMDP_Multichain_Criteria

open MarkovDecisionProcesses Filter
open scoped Topology

namespace PutermanMDP.Multichain

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A] [Nonempty S]

/-- Proposition 9.2.2, p. 456 (PDF 472), exactly as printed.
The missing requirement δ ≠ d is deliberately not supplied: see finding F2. -/
theorem strict_improvement (M : StationaryMDP S A) (δ d : Rule M)
    (h : ImprovementCondition M δ d) : StrictNearOneImprovement M δ d := by sorry

end PutermanMDP.Multichain
