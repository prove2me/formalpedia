-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_rhs19_antitone_t
-- name    : ShockCBM.ControlLimit.rhs19_antitone_t
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T00:10:13.031677+00:00
-- url     : https://prove2.me/theorems/00058c45-8a96-433f-b025-80bfb8088b9b
-- title:
--   Proof of Theorem 1, p. 33 — the continuation value $\mathbb E_s[V(s+A(s))]$ (RHS of (19)) is nonincreasing in the age $t$
-- statement:
--   Consider the collapsed MDP of the shock degradation model under its standing assumptions ($\alpha_0,\beta_0,a_0,b_0>0$, $0<c_p<c_u$, $0<\gamma<1$, $\xi\ge1$, $h\ge0$, and the conjugate kernel normalisable at $(a_0+x,b_0+n)$ for all $x,n\in\mathbb N$), with value function $V$ and one-period transition $s=(x,n,t)\mapsto s+A(s)=(x+Z(s),\,n+K(s),\,t+1)$, where $(Z(s),K(s))$ has the joint predictive pmf at the hyperparameters $\alpha=\alpha_0+n$, $\beta=\beta_0+t$, $a=a_0+x$, $b=b_0+n$.
--
--   Then the expected continuation value, i.e. the right-hand side of Inequality (19) divided by $\gamma$,
--   $$t\;\longmapsto\;\mathbb E_{(x,n,t)}\big[V\big((x,n,t)+A(x,n,t)\big)\big]=\sum_{z,k\in\mathbb N}\mathbb P_{(x,n,t)}[Z=z,K=k]\;V(x+z,\,n+k,\,t+1),$$
--   is non-increasing in the age $t$ for every fixed degradation level $x$ and shock count $n$: if $t\le t'$ then
--   $$\mathbb E_{(x,n,t')}[V(s+A(s))]\le\mathbb E_{(x,n,t)}[V(s+A(s))].$$
--
--   In the paper this is the step "the right-hand side of Inequality (19) is non-increasing in $t$ by part (i) of Lemma 2" in the proof of Theorem 1 (the same monotonicity is used for the iterates $V^m$ in the proof of Lemma 2(i), p. 32). Note that changing $t$ changes the law of the shock count $K(s)$ (rate parameter $\beta_0+t$), and $V$ need not be monotone in $n$ (p. 15), so this does not follow from Lemma 2(i) and Proposition 2(i) alone.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, proof of Theorem 1, p. 33 (right-hand side of (19))

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem rhs19_antitone_t (M : Model) (hM : M.Standing) (x n t t' : ℕ) (htt : t ≤ t') :
    M.Enext (x, n, t') M.V ≤ M.Enext (x, n, t) M.V := by sorry

end ShockCBM.ControlLimit
