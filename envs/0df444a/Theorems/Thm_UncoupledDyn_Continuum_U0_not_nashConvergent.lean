-- Prove2me | Theorems.Thm_UncoupledDyn_Continuum_U0_not_nashConvergent
-- name    : UncoupledDyn.Continuum.U0_not_nashConvergent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:30.413369+00:00
-- url     : https://prove2.me/theorems/afe94907-a471-4822-8192-1af2061765a5
-- title:
--   §II, pp. 1831–1832 — every uncoupled dynamic for 𝒰₀ is not Nash-convergent
-- statement:
--   Let $\mathcal U_0$ be the family of two-player games on the unit disk with payoffs $u^i(x^i,x^j)=-\|x^i-\xi^i(x^j)\|^2$, where $\xi^1,\xi^2:D\to D$ are continuous and each equation $\xi^i(\xi^j(x^i))=x^i$ has a unique solution. Then no dynamic $\dot x=F(x;\Gamma)$ for $\mathcal U_0$ is both uncoupled and Nash-convergent:
--   $$F\text{ uncoupled for }\mathcal U_0\ \Longrightarrow\ F\text{ is not Nash-convergent for }\mathcal U_0.$$
--
--   This is the main-text form of the impossibility result; the Appendix upgrades it from $\mathcal U_0$ to any family containing the games of $\mathcal U_0$ near $\Gamma_0$.
--
--   **Formalization Note.** Nash-convergence includes the regularity the paper always imposes ($C^1$ on $X$, all eigenvalues of the Jacobian at the equilibrium with negative real parts). Every game of $\mathcal U_0$ has a single Nash equilibrium (milestone on $\mathcal U_0$), so no extra hypothesis is needed.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), pp. 1831–1832, §II, "We will now prove that every uncoupled dynamic for 𝒰₀ is not Nash-convergent" and the concluding paragraph after Lemma 3

import Mathlib
import Definitions.Def_UncoupledDyn_Continuum_Setting

namespace UncoupledDyn.Continuum

/-- §II, pp. 1831–1832: every uncoupled dynamic for `𝒰₀` is not Nash-convergent. -/
theorem U0_not_nashConvergent (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) (hF : Uncoupled U0 F) :
    ¬ NashConvergent U0 F := by sorry

end UncoupledDyn.Continuum
