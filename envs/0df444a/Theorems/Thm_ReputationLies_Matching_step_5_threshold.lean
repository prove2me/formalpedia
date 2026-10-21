-- Prove2me | Theorems.Thm_ReputationLies_Matching_step_5_threshold
-- name    : ReputationLies.Matching.step_5_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:57.22536+00:00
-- url     : https://prove2.me/theorems/82662c29-186a-49de-bf85-546306273b90
-- title:
--   Proof of Proposition 1, Step 5, eqs. (12)–(13), p. 39 (PDF 41) — the lying benefit is strictly increasing with maximum B̄; unique interior threshold
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   Let
--   $$\Lambda(b) = b\,\frac{F(s_R(b)) - F(s_L)}{F(s_R(b))}$$
--   be the left-hand side of the threshold equation (12), $\Lambda(b^*) = L(r)$. Then:
--   1. $\Lambda$ is strictly increasing and continuous on $(0,1]$;
--   2. its value at $b = 1$ is
--   $$\bar B = \frac{F(s_H) - F(s_L)}{F(s_H)}; \tag{13}$$
--   3. for every level $\ell$ with $0 < \ell < \bar B$ there is a unique $b \in (0,1)$ with $\Lambda(b) = \ell$.
--
--   With $\ell = L(r)$, item 3 is the interior solution of (12) for advisers with $L(r) < \bar B$; the corner case $L(r) \ge \bar B$, $b^* = 1$, is part of Proposition 1.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 39 (PDF 41), proof of Proposition 1, Step 5, eqs. (12)–(13)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proof of Proposition 1, Step 5, eqs. (12)–(13), p. 39: the left-hand side of (12),
`b [F(sR(b)) − F(sL)] / F(sR(b))`, is strictly increasing and continuous on `(0, 1]`, its value
at `b = 1` is `B̄`, and for every level `0 < ℓ < B̄` there is a unique `b ∈ (0, 1)` at which it
equals `ℓ`. -/
theorem step_5_threshold (P : Primitives) (hP : P.Standing) :
    StrictMonoOn P.lieGain (Ioc 0 1) ∧ ContinuousOn P.lieGain (Ioc 0 1) ∧
    P.lieGain 1 = P.Bbar ∧
    ∀ ℓ : ℝ, 0 < ℓ → ℓ < P.Bbar → ∃! b : ℝ, b ∈ Ioo (0 : ℝ) 1 ∧ P.lieGain b = ℓ := by sorry

end ReputationLies.Matching
