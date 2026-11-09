-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_scale_geometry
-- name    : RankingQueryCost.Joint.scale_geometry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:26:14.487718+00:00
-- url     : https://prove2.me/theorems/751b3434-9a98-402c-a83a-4d581d9b006d
-- title:
--   Equation (3) and §5.1 — Finite extremal scale and incidence energy
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   For every admissible $n,s$, the finite graph extremum equals the maximum of the quasi-complete and quasi-star formulas computed in §5.1. Moreover,
--
--   $$U_{AK}=\max\{Q_C,Q_S\},\qquad B_s/3\le U\le B_s,\qquad B_s/2\le u\le B_s,$$
--
--   and every incidence flow supported on at most $s$ identities with $|c_e|\le1$ has squared norm at most $U$. This records equation (3) and the finite extremal identification as proof obligations. No asymptotic substitute for $U$ is used in the threshold.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §3.1, equation (3), p. 6, PDF p. 7; §5.1, p. 25, PDF p. 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Flow

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Equation (3), p. 6 / PDF 7, and the extremal formulas of §5.1, p. 25 / PDF 26. -/
theorem scale_geometry (n s : ℕ) (hadm : Admissible n s) :
    extremalDegreeEnergy n s = max (quasiCompleteEnergy n s) (quasiStarEnergy n s) ∧
    (incidenceCap n s : ℝ) / 3 ≤ (errorScale n s : ℝ) ∧
    errorScale n s ≤ incidenceCap n s ∧
    (incidenceCap n s : ℝ) / 2 ≤ (crudeScale n s : ℝ) ∧
    crudeScale n s ≤ incidenceCap n s ∧
    ∀ (E : Finset (Pair n)) (c : Pair n → ℝ), E.card ≤ s → (∀ e ∈ E, |c e| ≤ 1) →
      euclideanNorm (flow E c) ^ 2 ≤ (errorScale n s : ℝ) := by sorry

end RankingQueryCost.Joint
