-- Prove2me | Theorems.Thm_SpinStatistics_ehrenfest_oppenheimer
-- name    : SpinStatistics.ehrenfest_oppenheimer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:08:51.387206+00:00
-- url     : https://prove2.me/theorems/f20e4bc1-dd72-4dee-9476-9d6502ec8dbd
-- title:
--   Ehrenfest–Oppenheimer theorem: composites inherit the spin–statistics relation
-- statement:
--   Consider two composite particles with identical internal structure, each made of $k$ constituents, where the constituent in slot $i$ has doubled spin $s_i\in\mathbb N$ (spin $s_i/2$). Assume the constituents obey the spin–statistics relation: exchanging the two identical constituents in slot $i$ multiplies the many-body wavefunction by $(-1)^{s_i}$ (antisymmetric for half-integer spin, symmetric for integer spin),
--   $$\Psi(c\circ\tau_i)=(-1)^{s_i}\,\Psi(c).$$
--   Let $J$ be a doubled total spin of a composite obtainable by addition of angular momenta of $s_1,\dots,s_k$. Then the composites obey the same relation:
--   $$\Psi(c\circ\sigma)=(-1)^{J}\,\Psi(c)\qquad\text{for all } c.$$
--   So a composite with an even number of constituent fermions has integer spin and a symmetric wavefunction (a boson), and one with an odd number has half-integer spin and an antisymmetric wavefunction (a fermion).
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Composite particles', p. 4, first paragraph (the result 'called the Ehrenfest-Oppenheimer theorem')

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem ehrenfest_oppenheimer {X : Type*} {k : ℕ} (s : Fin k → ℕ)
    (Ψ : (Fin 2 × Fin k → X) → ℂ)
    (hexch : ∀ i c, Ψ (c ∘ swapConstituent i) = (-1) ^ s i * Ψ c)
    (J : ℕ) (hJ : CanAddTo (List.ofFn s) J) :
    ∀ c, Ψ (c ∘ swapComposites) = (-1) ^ J * Ψ c := by sorry

end SpinStatistics
