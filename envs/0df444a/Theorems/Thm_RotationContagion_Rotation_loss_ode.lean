-- Prove2me | Theorems.Thm_RotationContagion_Rotation_loss_ode
-- name    : RotationContagion.Rotation.loss_ode
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:47.934862+00:00
-- url     : https://prove2.me/theorems/535dee31-201d-4f1b-9c2a-42ce92e329ef
-- title:
--   §2.1, p. 7 — the loss ℓ solves the logistic equation with ℓ(0) = 1/K
-- statement:
--   Let $\gamma > 0$, $K > 1$, $R \ge 0$, let $b = \frac1\gamma \ln(K-1)$ and $\ell(t) = e^{\gamma(t-b)}/(1+e^{\gamma(t-b)})$. Then $\ell$ is the solution of the logistic differential equation
--   $$\dot\ell(t) = \gamma\,\ell(t)\,(1-\ell(t)) \quad\text{for all } t \in \mathbb R, \qquad \ell(0) = \frac1K.$$
--
--   So $\ell(t)$ is the prevalence in a group in which the disease spreads without interruption for $t$ units of time, starting from measure one of infected in a group of size $K$. This is what links the loss to the prevalence dynamics (2) in Lemma 1.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 7, §2.1 (definition of the loss ℓ)

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

/-- §2.1, p. 7: the loss `ℓ` solves the logistic equation `ℓ̇ = γ ℓ (1 - ℓ)` with `ℓ(0) = 1/K`. -/
theorem loss_ode (P : Params) (hP : P.Standing) :
    loss P 0 = 1 / P.K ∧
      ∀ t : ℝ, HasDerivAt (loss P) (P.γ * loss P t * (1 - loss P t)) t := by sorry

end RotationContagion.Rotation
