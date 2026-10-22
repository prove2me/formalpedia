-- Prove2me | Theorems.Thm_RiskPersuasion_Binary_lemma_3
-- name    : RiskPersuasion.Binary.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:33.294097+00:00
-- url     : https://prove2.me/theorems/114e1539-8419-436d-8c54-1aba08000bc7
-- title:
--   Lemma 3 — a quasiconvex differential utility ρ̂ satisfies Assumption 2
-- statement:
--   Suppose the receiver's differential utility $\hat\rho(\mu)=\rho(\mu,1)-\rho(\mu,0)$ is quasiconvex on the simplex $\Delta(\Omega)$, i.e. every sublevel set $\{\mu\in\Delta(\Omega):\hat\rho(\mu)\le r\}$ is convex. Then Assumption 2 holds: the set
--   $$P_1^c=\{\mu\in\Delta(\Omega):\ \hat\rho(\mu)<0\}$$
--   is convex.
--
--   The lemma gives a checkable sufficient condition for Assumption 2; for instance it applies when $\rho(\cdot,1)$ is convex and $\rho(\cdot,0)$ is concave.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 22, Lemma 3 (proof p. 40)

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

namespace RiskPersuasion.Binary

theorem lemma_3 {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : (Ω → ℝ) → Fin 2 → ℝ)
    (hq : QuasiconvexOn ℝ (stdSimplex ℝ Ω) (ρhat ρ)) :
    Assumption2 ρ := by sorry

end RiskPersuasion.Binary
