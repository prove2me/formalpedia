-- Prove2me | Theorems.Thm_SpinStatistics_commuting_fields_symmetric_part
-- name    : SpinStatistics.commuting_fields_symmetric_part
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T13:52:42.576788+00:00
-- url     : https://prove2.me/theorems/fe2434a2-1c2c-4a15-a279-30f99a48fb77
-- title:
--   Commuting fields: only the symmetric part of $\psi$ contributes (bosons)
-- statement:
--   Let $X$ be a finite set of positions, $A$ a complex algebra (of operators), $\phi : X\to A$ a field and $\psi : X\times X\to\mathbb C$ a two-particle wavefunction. Write
--   $$\Phi[\psi]=\sum_{x\ne y}\psi(x,y)\,\phi(x)\phi(y)$$
--   for the two-particle creation operator. If the field **commutes** at distinct points,
--   $$\phi(x)\phi(y)=\phi(y)\phi(x)\qquad (x\ne y),$$
--   then only the symmetric part of $\psi$ contributes:
--   $$\Phi[\psi]=\Phi[\psi_S]\qquad\text{and}\qquad \Phi[\psi_A]=0,$$
--   where $\psi_S(x,y)=\tfrac12(\psi(x,y)+\psi(y,x))$ and $\psi_A(x,y)=\tfrac12(\psi(x,y)-\psi(y,x))$. So one may take $\psi(x,y)=\psi(y,x)$, and the field creates bosons.
--
--   **Formalization Note.** The integral $\iint$ is replaced by a finite sum over distinct positions (the source assumes $x\ne y$).
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Exchange symmetry or permutation symmetry', p. 2 (commuting case)

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem commuting_fields_symmetric_part {X A : Type*} [Fintype X] [DecidableEq X]
    [Ring A] [Algebra ℂ A] (ψ : X → X → ℂ) (φ : X → A)
    (hcomm : ∀ x y, x ≠ y → φ x * φ y = φ y * φ x) :
    twoParticleOp ψ φ = twoParticleOp (symmPart ψ) φ ∧
      twoParticleOp (antisymmPart ψ) φ = 0 := by sorry

end SpinStatistics
