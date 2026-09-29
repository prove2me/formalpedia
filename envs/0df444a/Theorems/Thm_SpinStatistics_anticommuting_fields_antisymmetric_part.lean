-- Prove2me | Theorems.Thm_SpinStatistics_anticommuting_fields_antisymmetric_part
-- name    : SpinStatistics.anticommuting_fields_antisymmetric_part
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:27:20.075979+00:00
-- url     : https://prove2.me/theorems/2cd9f4cc-1d55-4a38-897f-be8475b14794
-- title:
--   Anticommuting fields: only the antisymmetric part of $\psi$ contributes (fermions)
-- statement:
--   Let $X$ be a finite set of positions, $A$ a complex algebra (of operators), $\phi : X\to A$ a field and $\psi : X\times X\to\mathbb C$ a two-particle wavefunction, with $\Phi[\psi]=\sum_{x\ne y}\psi(x,y)\,\phi(x)\phi(y)$. If the field **anticommutes** at distinct points,
--   $$\phi(x)\phi(y)=-\phi(y)\phi(x)\qquad (x\ne y),$$
--   then only the antisymmetric part of $\psi$ contributes:
--   $$\Phi[\psi]=\Phi[\psi_A]\qquad\text{and}\qquad \Phi[\psi_S]=0.$$
--   So one may take $\psi(x,y)=-\psi(y,x)$, and the particles are fermions.
--
--   **Formalization Note.** The integral is replaced by a finite sum over distinct positions (the source assumes $x\ne y$); nothing is assumed about $\phi(x)^2$.
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Exchange symmetry or permutation symmetry', p. 2 (anticommuting case)

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem anticommuting_fields_antisymmetric_part {X A : Type*} [Fintype X] [DecidableEq X]
    [Ring A] [Algebra ℂ A] (ψ : X → X → ℂ) (φ : X → A)
    (hanti : ∀ x y, x ≠ y → φ x * φ y = -(φ y * φ x)) :
    twoParticleOp ψ φ = twoParticleOp (antisymmPart ψ) φ ∧
      twoParticleOp (symmPart ψ) φ = 0 := by sorry

end SpinStatistics
