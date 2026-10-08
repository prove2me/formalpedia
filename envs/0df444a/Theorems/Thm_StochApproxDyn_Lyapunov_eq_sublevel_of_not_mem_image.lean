-- Prove2me | Theorems.Thm_StochApproxDyn_Lyapunov_eq_sublevel_of_not_mem_image
-- name    : StochApproxDyn.Lyapunov.eq_sublevel_of_not_mem_image
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:12:13.332876+00:00
-- url     : https://prove2.me/theorems/2b05c5ec-a841-4193-8c92-7de326ad040c
-- title:
--   §6.2, proof of Proposition 6.4, p. 27 — $L=L_c$ for every value $c>v^*$ with $c\notin V(\Lambda)$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$, let $\Lambda\subset M$ be a compact invariant set and let $V:M\to\mathbb R$ be a Lyapounov function for $\Lambda$. Let $L\subset M$ be an internally chain transitive set and $v^*=\inf\{V(x):x\in L\}$. Let $c\in\mathbb R$ with
--   $$c\notin V(\Lambda)\qquad\text{and}\qquad c>v^* .$$
--   Then
--   $$L=L_c:=\{x\in L: V(x)<c\},$$
--   that is, $V(x)<c$ for every $x\in L$.
--
--   In the proof of Proposition 6.4, the values $c=v_n$ form a sequence in $\mathbb R\setminus V(\Lambda)$ decreasing to $v^*$, which exists because $V(\Lambda)$ has empty interior; intersecting the sets $L_{v_n}$ then gives $V\equiv v^*$ on $L$. The paper obtains $L=L_c$ by showing $\Phi_t(\overline{L_c})\subset L_c$ for $t>0$ and applying Lemma 5.2 and Proposition 5.3 to $\Phi|L$.
--
--   **Formalization Note** \"$v^*$ is the infimum\" is `IsGLB (V '' L) vstar`; the set $L_c$ is written as `{x ∈ L | V x < c}`.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 27, Section 6.2, proof of Proposition 6.4 (second paragraph: L = L_n)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction

open scoped NNReal

namespace StochApproxDyn.Lyapunov

/-- The sublevel step in the proof of Proposition 6.4 (Benaïm 1999, §6.2, p. 27). Let `V` be a
Lyapounov function for the compact invariant set `Λ`, `L` an internally chain transitive set,
`v* = inf {V x : x ∈ L}`, and `c` a real number with `c ∉ V(Λ)` and `c > v*`. Then
`L = L_c := {x ∈ L : V x < c}`. -/
theorem eq_sublevel_of_not_mem_image {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (L : Set M) (hL : StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ L)
    (vstar : ℝ) (hvstar : IsGLB (V '' L) vstar)
    (c : ℝ) (hcΛ : c ∉ V '' Λ) (hc : vstar < c) :
    L = {x ∈ L | V x < c} := by sorry

end StochApproxDyn.Lyapunov
