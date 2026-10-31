-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_5
-- name    : RobustPrefLearn.MTP.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:07.846648+00:00
-- url     : https://prove2.me/theorems/8b826a2b-e42b-4445-a747-3fbfd7b2925d
-- title:
--   Theorem 5, p. 18 — the Myopic Tracking Policy is worst-case asymptotically optimal
-- statement:
--   Let $K\ge2$ versions and $0<p<1$. There is a threshold $\beta=\beta(\delta)>0$ such that, for every choice of the arbitrary initial display set $S_1$ of Algorithm 1, the Myopic Tracking Policy $\mathrm{MTP}_{\beta(\delta)}$ satisfies
--   $$\mathrm{MTP}\in\arg\min_{\Pi\ \text{accurate}}\ \sup_{f\in\mathcal M_p}\ \limsup_{\delta\downarrow0}\frac{\mathbb E^{\pi_\delta}_f[\tau]}{\log(1/\delta)}. \tag{9}$$
--   That is:
--
--   1. the family $\{\mathrm{MTP}_{\beta(\delta)}\}_{\delta}$ is accurate (each member is $\delta$-accurate over $\mathcal M_p$), and
--   2. its worst-case rate $\sup_{f\in\mathcal M_p}\limsup_{\delta\downarrow0}\mathbb E_f[\tau]/\log(1/\delta)$ is at most that of every accurate family of admissible policies.
--
--   This is the main result: a simple, likelihood-based display policy learns the most preferred version with the smallest possible worst-case number of votes, uniformly over the class of $p$-separable preferences.
--
--   **Formalization Note** Rates take values in $[0,\infty]$. The accuracy conjunct is part of the argmin and cannot be dropped (without it a tiny threshold stops after one vote). The common optimal value is $1/I^{\mathrm{OA}}_*$ (proof, p. 21) but is not part of the statement. $\beta$ is chosen before $S_1$, so one threshold works for every initial display set (Algorithm 1 lets $S_1$ be arbitrary). Policies decide when to stop and what to select as functions of the observed history, as in the paper's definition. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 18, Theorem 5, (9); proof p. 21

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 5, p. 18 (worst-case asymptotic optimality of MTP). There is a threshold
`β = β(δ) > 0` such that, whatever the arbitrary initial display set `S₁` of Algorithm 1, the Myopic
Tracking family `{MTP_{β(δ)}}` is accurate and minimizes
`sup_{f ∈ M_p} limsup_{δ ↓ 0} E^{π_δ}_f[τ]/log(1/δ)` over all accurate families. -/
theorem theorem_5 (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ β : ℝ → ℝ, (∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < β δ) ∧ ∀ S1 : DS K,
      IsAccurate p (fun δ => mtp p S1 (β δ)) ∧
      ∀ fam : ℝ → Policy K, IsAccurate p fam →
        worstRate p (fun δ => mtp p S1 (β δ)) ≤ worstRate p fam := by sorry

end RobustPrefLearn.MTP
