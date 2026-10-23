-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_7
-- name    : RobustPrefLearn.MTP.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:54.117984+00:00
-- url     : https://prove2.me/theorems/70088743-b9a4-4efc-9581-6ffb33ffd696
-- title:
--   Theorem 7, p. 20 — MTP is δ-accurate whenever β ≥ C_1 + log(1/δ), with C_1 depending only on K
-- statement:
--   Let $K\ge2$. There is a constant $C_1$, depending only on $K$, such that for every $p\in(0,1)$, every initial display set $S_1$, every $\delta\in(0,1)$ and every threshold
--   $$\beta\ \ge\ C_1+\log\tfrac1\delta,$$
--   the Myopic Tracking Policy with threshold $\beta$ is $\delta$-accurate: it is admissible, and for every $f\in\mathcal M_p$ it stops almost surely and selects the top-ranked version of $f$ with probability at least $1-\delta$.
--
--   Section 8 uses $C_1=\log((K-1)(K-1)!)$. With Theorem 6 this makes MTP an accurate family whose worst-case rate is $1/I^{\mathrm{OA}}_*$.
--
--   **Formalization Note** $C_1$ is quantified after $K$ and before $p$, $S_1$ and $\delta$. $\delta$-accuracy includes admissibility of MTP (its display probabilities sum to one) and $\mathbb P_f(\tau<\infty)=1$ for every $f\in\mathcal M_p$. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 20, Theorem 7

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-- Theorem 7, p. 20 (accuracy of MTP). There is a constant `C₁`, depending only on `K`, such that
for every `p`, every initial display set `S₁` and every `δ ∈ (0, 1)`, the Myopic Tracking Policy
with any threshold `β ≥ C₁ + log(1/δ)` is `δ`-accurate. -/
theorem theorem_7 (K : ℕ) [NeZero K] (hK : 2 ≤ K) :
    ∃ C1 : ℝ, ∀ p : ℝ, 0 < p → p < 1 → ∀ (S1 : DS K), ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ β : ℝ,
      C1 + Real.log (1 / δ) ≤ β → IsDeltaAccurate p δ (mtp p S1 β) := by sorry

end RobustPrefLearn.MTP
