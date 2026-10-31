-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_rhs19_monotone_x
-- name    : ShockCBM.ControlLimit.rhs19_monotone_x
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T00:09:56.109573+00:00
-- url     : https://prove2.me/theorems/739a0ba0-e98c-4986-bc34-91774dc759c6
-- title:
--   Proof of Theorem 1, p. 33 — the continuation value $\mathbb E_s[V(s+A(s))]$ (RHS of (19)) is nondecreasing in the degradation level $x$
-- statement:
--   Consider the collapsed MDP of the shock degradation model under its standing assumptions ($\alpha_0,\beta_0,a_0,b_0>0$, $0<c_p<c_u$, $0<\gamma<1$, $\xi\ge1$, $h\ge0$, and the conjugate kernel normalisable at $(a_0+x,b_0+n)$ for all $x,n\in\mathbb N$), with value function $V$ and one-period transition $s=(x,n,t)\mapsto s+A(s)=(x+Z(s),\,n+K(s),\,t+1)$, where $(Z(s),K(s))$ has the joint predictive pmf at the hyperparameters $\alpha=\alpha_0+n$, $\beta=\beta_0+t$, $a=a_0+x$, $b=b_0+n$.
--
--   Then the expected continuation value, i.e. the right-hand side of Inequality (19) divided by $\gamma$,
--   $$x\;\longmapsto\;\mathbb E_{(x,n,t)}\big[V\big((x,n,t)+A(x,n,t)\big)\big]=\sum_{z,k\in\mathbb N}\mathbb P_{(x,n,t)}[Z=z,K=k]\;V(x+z,\,n+k,\,t+1),$$
--   is non-decreasing in $x$ for every fixed shock count $n$ and age $t$: if $x\le x'$ then
--   $$\mathbb E_{(x,n,t)}[V(s+A(s))]\le\mathbb E_{(x',n,t)}[V(s+A(s))].$$
--
--   In the paper this is the step "Based on part (ii) of Lemma 2, the right-hand side of Inequality (19) is non-decreasing in $x$" in the proof of Theorem 1; it combines Lemma 2(ii) ($V$ non-decreasing in $x$) with the stochastic monotonicity in $x$ of the damage increment (Proposition 2(ii)), the law of $K(s)$ being independent of $x$.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, proof of Theorem 1, p. 33 (right-hand side of (19))

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem rhs19_monotone_x (M : Model) (hM : M.Standing) (x x' n t : ℕ) (hxx : x ≤ x') :
    M.Enext (x, n, t) M.V ≤ M.Enext (x', n, t) M.V := by sorry

end ShockCBM.ControlLimit
