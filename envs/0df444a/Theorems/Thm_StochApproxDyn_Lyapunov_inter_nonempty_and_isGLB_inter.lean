-- Prove2me | Theorems.Thm_StochApproxDyn_Lyapunov_inter_nonempty_and_isGLB_inter
-- name    : StochApproxDyn.Lyapunov.inter_nonempty_and_isGLB_inter
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:11:57.12098+00:00
-- url     : https://prove2.me/theorems/db6d54b5-c4da-4fdd-9bde-0b3e11640495
-- title:
--   §6.2, proof of Proposition 6.4, p. 27 — an internally chain transitive set meets $\Lambda$, and $\inf_L V=\inf_{L\cap\Lambda}V$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$, let $\Lambda\subset M$ be a compact invariant set and let $V:M\to\mathbb R$ be a Lyapounov function for $\Lambda$. Let $L\subset M$ be an internally chain transitive set and
--   $$v^*=\inf\{V(x):x\in L\}.$$
--   Then $L\cap\Lambda\neq\emptyset$ and
--   $$v^*=\inf\{V(x):x\in L\cap\Lambda\}.$$
--
--   This is the claim with which the proof of Proposition 6.4 begins. It does not use the hypothesis that $V(\Lambda)$ has empty interior. Since $L\cap\Lambda$ is compact and nonempty, it shows in particular that the minimum of $V$ on $L$ is attained on $L\cap\Lambda$.
--
--   **Formalization Note** \"$v^*$ is the infimum\" is stated as `IsGLB (V '' L) vstar`, so no junk value of a real `sInf` can enter; both infima exist since $L$ and $L\cap\Lambda$ are compact and $V$ is continuous.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 27, Section 6.2, proof of Proposition 6.4 (the claim)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction

open scoped NNReal

namespace StochApproxDyn.Lyapunov

/-- The claim in the proof of Proposition 6.4 (Benaïm 1999, §6.2, p. 27). Let `V` be a
Lyapounov function for the compact invariant set `Λ`, and `L` an internally chain transitive set
with `v* = inf {V x : x ∈ L}`. Then `L ∩ Λ ≠ ∅` and `v* = inf {V x : x ∈ L ∩ Λ}`. No assumption
on the interior of `V(Λ)` is needed. -/
theorem inter_nonempty_and_isGLB_inter {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (L : Set M) (hL : StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ L)
    (vstar : ℝ) (hvstar : IsGLB (V '' L) vstar) :
    (L ∩ Λ).Nonempty ∧ IsGLB (V '' (L ∩ Λ)) vstar := by sorry

end StochApproxDyn.Lyapunov
