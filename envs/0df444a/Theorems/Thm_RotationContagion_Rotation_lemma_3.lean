-- Prove2me | Theorems.Thm_RotationContagion_Rotation_lemma_3
-- name    : RotationContagion.Rotation.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:43.728222+00:00
-- url     : https://prove2.me/theorems/68f622ad-1f03-460c-92b1-e1db21a5d455
-- title:
--   Lemma 3, pp. 9–10 — ℓ(τ) + ℓ(R − τ) is U-shaped if R/2 < b and hump-shaped if R/2 > b
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$, and let $f(\tau) = \ell(\tau) + \ell(R-\tau)$ for $\tau \in \mathbb R$.
--
--   1. If it takes more than half of the reaction time to infect half of the group, $R/2 < b$, then $f$ is U-shaped: it is strictly decreasing on $(-\infty, R/2]$ and strictly increasing on $[R/2, \infty)$.
--   2. If it takes less than half of the reaction time to infect half of the group, $R/2 > b$, then $f$ is hump-shaped: it is strictly increasing on $(-\infty, R/2]$ and strictly decreasing on $[R/2, \infty)$.
--
--   The shape of $f$ decides whether risk over the exposure time is undesirable (U-shape) or desirable (hump), and so which schedule solves (P2) and (P1).
--
--   **Formalization Note** The page says "for $\tau < R/2$" and "for $\tau > R/2$" with no domain; the statement is made on all of $\mathbb R$, which contains any restriction to $[0,R]$.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), pp. 9–10, Lemma 3

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

/-- Lemma 3, pp. 9–10: if `R/2 < b`, then `ℓ(τ) + ℓ(R - τ)` decreases for `τ < R/2` and increases
for `τ > R/2`; if `R/2 > b`, it increases for `τ < R/2` and decreases for `τ > R/2`. -/
theorem lemma_3 (P : Params) (hP : P.Standing) :
    (P.R / 2 < b P →
      StrictAntiOn (relaxedObj P) (Set.Iic (P.R / 2)) ∧
        StrictMonoOn (relaxedObj P) (Set.Ici (P.R / 2))) ∧
    (b P < P.R / 2 →
      StrictMonoOn (relaxedObj P) (Set.Iic (P.R / 2)) ∧
        StrictAntiOn (relaxedObj P) (Set.Ici (P.R / 2))) := by sorry

end RotationContagion.Rotation
