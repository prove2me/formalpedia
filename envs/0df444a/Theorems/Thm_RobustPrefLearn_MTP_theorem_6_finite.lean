-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_6_finite
-- name    : RobustPrefLearn.MTP.theorem_6_finite
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T14:49:09.85208+00:00
-- url     : https://prove2.me/theorems/b105eb63-c95f-4ea8-a8d4-27eb64cd3e58
-- title:
--   Theorem 6, p. 20, first sentence — MTP has finite expected sample size E_f[τ] < ∞
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. For every threshold $\beta$, every initial display set $S_1$ and every preference $f\in\mathcal M_p$, the Myopic Tracking Policy $\mathrm{MTP}_\beta$ of Algorithm 1 stops after a number of votes with finite expectation:
--   $$\mathbb E_f[\tau]<\infty .$$
--
--   This is the first assertion of Theorem 6 ("$\mathbb E_f[\tau]<\infty$ for every $\delta>0$ under the Myopic Tracking Policy"), stated for a single fixed threshold. It also gives $\mathbb P_f(\tau<\infty)=1$, which is part of the $\delta$-accuracy of MTP in Theorem 7.
--
--   **Formalization Note** The paper states this for thresholds $\beta=\beta(\delta)\le C_0+\log(1/\delta)$. Since $\delta$ enters only through $\beta$, the statement is given for each fixed real $\beta$; no sign condition on $\beta$ is needed. $\mathbb E_f[\tau]=\sum_{t\ge0}\mathbb P_f(\tau>t)\in[0,\infty]$ as in `expTau`. The hypotheses $K\ge2$ and $0<p<1$ are added as in the parent milestone `RobustPrefLearn.MTP.theorem_6`.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 20, Theorem 6 (first sentence)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 6, p. 20, first sentence (finiteness of the expected sample size): for every threshold
`β`, every initial display set `S₁` and every `f ∈ M_p`, the Myopic Tracking Policy has
`E_f[τ] < ∞`. -/
theorem theorem_6_finite (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (β : ℝ) (S1 : DS K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) :
    expTau (mtp p S1 β) f < ⊤ := by sorry

end RobustPrefLearn.MTP
