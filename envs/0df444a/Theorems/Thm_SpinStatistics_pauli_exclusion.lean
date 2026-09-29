-- Prove2me | Theorems.Thm_SpinStatistics_pauli_exclusion
-- name    : SpinStatistics.pauli_exclusion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:32:10.802089+00:00
-- url     : https://prove2.me/theorems/e467f3e7-91f5-41d2-9d3b-682086859951
-- title:
--   Pauli exclusion principle for antisymmetric two-particle wavefunctions
-- statement:
--   Let $X$ be the set of one-particle states.
--
--   1. (**Fermions.**) If a two-particle wavefunction $\psi : X\times X\to\mathbb C$ is antisymmetric, $\psi(x,y)=-\psi(y,x)$ for all $x,y$, then
--   $$\psi(x,x)=0\qquad\text{for every } x\in X,$$
--   i.e. the amplitude for two identical fermions to occupy the same state is zero.
--   2. (**Bosons.**) The rule does not hold for bosons: for every $x\in X$ there is a symmetric wavefunction ($\psi(y,z)=\psi(z,y)$ for all $y,z$) with $\psi(x,x)\ne0$.
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Exchange symmetry or permutation symmetry', p. 2, first paragraph

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem pauli_exclusion {X : Type*} :
    (∀ ψ : X → X → ℂ, (∀ x y, ψ x y = -ψ y x) → ∀ x, ψ x x = 0) ∧
      (∀ x : X, ∃ ψ : X → X → ℂ, (∀ y z, ψ y z = ψ z y) ∧ ψ x x ≠ 0) := by sorry

end SpinStatistics
