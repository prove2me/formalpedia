-- Prove2me | Theorems.Thm_RotationContagion_Rotation_lemma_1
-- name    : RotationContagion.Rotation.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:01.51843+00:00
-- url     : https://prove2.me/theorems/06e846c4-fc26-4a0a-9500-6969066735b2
-- title:
--   Lemma 1, p. 7 — the prevalence at the reaction time is ℓ(τ)
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$. Let $r$ be a rotation schedule, $\omega \in \{0,1\}$ the infected group and $t^* \ge 0$ the infection time. Then:
--
--   1. the function $t \mapsto \ell\!\left(\int_{t^*}^{t} r(\omega,s)\,ds\right)$ is a prevalence path, i.e. it solves equation (2) from $p_{t^*} = 1/K$;
--   2. every prevalence path $p$ of group $\omega$ after an infection at $t^*$ satisfies $p_t = \ell\!\left(\int_{t^*}^{t} r(\omega,s)\,ds\right)$ for all $t \ge t^*$, and in particular
--   $$p^\omega_{t^*+R}(\omega) = \ell(\tau), \qquad \tau = \int_{t^*}^{t^*+R} r(\omega,t)\,dt.$$
--
--   Terminal prevalence therefore depends on the schedule only through the exposure time, which reduces (P1) to a problem about the distribution of $\tau$.
--
--   **Formalization Note** Part 1 (existence of the solution) is added: the page presupposes that (2) has a solution. Part 2 is stated for every $t \ge t^*$, which contains the page's statement at $t = t^* + R$.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 7, Lemma 1

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

/-- Lemma 1, p. 7: for a schedule `r`, an infected group `ω` and an infection time `t0 ≥ 0`,
`t ↦ ℓ(∫_{t0}^t r(ω, s) ds)` is a prevalence path, and every prevalence path `p` satisfies
`p(t) = ℓ(∫_{t0}^t r(ω, s) ds)` for `t ≥ t0`; in particular `p(t0 + R) = ℓ(τ)`. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r)
    (ω : Fin 2) (t0 : ℝ) (ht0 : 0 ≤ t0) :
    IsPrevalencePath P r ω t0 (fun t => loss P (∫ s in t0..t, r ω s)) ∧
      ∀ p : ℝ → ℝ, IsPrevalencePath P r ω t0 p →
        (∀ t : ℝ, t0 ≤ t → p t = loss P (∫ s in t0..t, r ω s)) ∧
          p (t0 + P.R) = loss P (exposure P r ω t0) := by sorry

end RotationContagion.Rotation
