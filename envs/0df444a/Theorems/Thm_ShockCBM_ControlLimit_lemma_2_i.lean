-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_lemma_2_i
-- name    : ShockCBM.ControlLimit.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:31.42633+00:00
-- url     : https://prove2.me/theorems/4fd23bac-c72c-4d60-b8a3-9df09c8e6257
-- title:
--   Lemma 2(i), p. 15 — the value function V(x, n, t) is nonincreasing in the age t
-- statement:
--   Consider the collapsed MDP of the shock degradation model under its standing assumptions, with value function $V$ (the limit of value iteration from zero). Then $V$ is non-increasing in the age: for all $x,n\in\mathbb N$ and $t\le t'$,
--   $$V(x,n,t')\le V(x,n,t).$$
--
--   Together with part (ii) this monotonicity drives the structure of the optimal replacement policy; in particular it yields that the control limit is non-decreasing in age.
--
--   **Formalization Note** The published proof argues by induction on value iteration and needs the expectation $\mathbb E_s[V^m(s+A(s))]$ to be non-increasing in $t$; since $V^m$ is not monotone in the shock count $n$, that step is not justified as written. The statement is posed exactly as printed, without any monotonicity-in-$n$ hypothesis.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, p. 15, Lemma 2(i) (proof p. 32)

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem lemma_2_i (M : Model) (hM : M.Standing) (x n t t' : ℕ) (htt : t ≤ t') :
    M.V (x, n, t') ≤ M.V (x, n, t) := by sorry

end ShockCBM.ControlLimit
