-- Prove2me | Theorems.Thm_Penrose_self_energy_translation
-- name    : Penrose.self_energy_translation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:22:49.046287+00:00
-- url     : https://prove2.me/theorems/f47d0ba9-9231-463a-87c6-85901265efb7
-- title:
--   Self-energy is invariant under translation of the mass distribution
-- statement:
--   If a smooth, rapidly decreasing mass distribution $\rho'$ on $\mathbb{R}^3$ is a translate of $\rho$, in the sense that for some vector $v$
--
--   $$\rho'(x) = \rho(x - v) \quad\text{for all } x,$$
--
--   then for any real $G$ the gravitational self-energies coincide:
--
--   $$E(\rho) = E(\rho'), \qquad E(\sigma) = -\frac{G}{2}\iint \frac{\sigma(x)\sigma(y)}{\|x-y\|}\,dx\,dy.$$
--
--   The kernel $1/\|x-y\|$ depends only on the difference $x-y$, so the double integral is invariant under translating both arguments simultaneously. This is the structural fact behind the lump thought experiment of Section 2 of Penrose (1996, pp. 584–585): a rigid lump placed in two different locations gives two mass distributions that are translates of one another, so their individual gravitational self-energies are equal — the hypothesis under which the paper says either expression, the incompatibility measure or the interaction energy, determines the scale of the energy uncertainty (Section 6, p. 597).
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 2, pp. 584-585 (lump in two locations) and Section 6, p. 597 (equal individual self-energies)

import Mathlib
import Definitions.Def_penrose
import Definitions.Def_penrose_energy

open MeasureTheory

namespace Penrose

theorem self_energy_translation (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) (h : ∀ x, ⇑ρ' x = ⇑ρ (x - v)) :
    gravSelfEnergy G ρ = gravSelfEnergy G ρ' := by sorry

end Penrose
