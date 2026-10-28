-- Prove2me | Theorems.Thm_ReputationLies_Matching_eq_9_lying_condition
-- name    : ReputationLies.Matching.eq_9_lying_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:19:54.005051+00:00
-- url     : https://prove2.me/theorems/922cae98-16b1-427a-b6e3-f7930fe37259
-- title:
--   Proof of Proposition 1, Step 2, eq. (9), p. 38 (PDF 40) — a low-skill adviser strictly prefers to lie iff b[F(sR) − F(sNR)]/F(sR) > L(r)
-- statement:
--   Throughout, the standing assumptions of §2 hold: $0 < s_L < s_H < 1$, $p \in (0,1)$, $g(r) > 0$ and $c(r) \in (0,r)$ for $r > 0$, $v(0) = 0$ and $v' > 0$, Assumption (A1) $L' > 0$, and the bias and outside-option laws are continuous with full support on $[0,1]$, $F$ being $C^1$ on $[0,1]$.
--
--   Fix a reputation $r > 0$ and an equilibrium at $r$, with beliefs $s_R$ and $s_{NR}$. For every bias $b$, an adviser with a low-skilled candidate strictly prefers to recommend (lie) rather than not to recommend exactly when
--   $$U(R, s_L) > U(NR, s_L) \iff b\,\frac{F(s_R) - F(s_{NR})}{F(s_R)} > L(r). \tag{9}$$
--
--   The left-hand side is the relative gain in hiring probability from lying, scaled by the bias; the right-hand side is the reputation loss of eq. (1). This condition is what makes the low-skill adviser's equilibrium strategy a threshold rule.
--
--   **Formalization Note.** In an equilibrium the firm hires after message $m$ with probability $F(s_m)$, and $F(s_R) \ge F(s_L) > 0$, so the division is well defined.
-- source:
--   Câmara, Jia & Raffiee, Reputation, competition, and lies in labor market recommendations, authors' manuscript of Sept. 26, 2022 (Management Science, doi:10.1287/mnsc.2022.4654), p. 38 (PDF 40), proof of Proposition 1, Step 2, eq. (9)

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set

namespace ReputationLies.Matching

/-- Proof of Proposition 1, Step 2, eq. (9), p. 38: in an equilibrium at reputation `r > 0`, an
adviser with a low-skilled candidate and bias `b` strictly prefers to recommend iff
`b [F(sR) − F(sNR)] / F(sR) > L(r)`. -/
theorem eq_9_lying_condition (P : Primitives) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (σ : Profile) (hσ : IsEquilibrium P σ r) (b : ℝ) :
    utility P σ r b false false < utility P σ r b false true ↔
      P.L r < b * ((P.F σ.sR - P.F σ.sNR) / P.F σ.sR) := by sorry

end ReputationLies.Matching
