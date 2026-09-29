-- Prove2me | Theorems.Thm_SpinStatistics_composite_exchange_sign
-- name    : SpinStatistics.composite_exchange_sign
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:35:31.254881+00:00
-- url     : https://prove2.me/theorems/18014d61-d9b2-4ef4-bbb1-ddfa3c35df1a
-- title:
--   Exchange sign of two composite particles is $(-1)^{\#\text{fermions}}$
-- statement:
--   Consider two composite particles with identical internal structure, each made of $k$ constituents; slot $i$ of either composite holds the same species of elementary particle, which is a fermion or a boson. A configuration $c$ assigns a one-particle state in $X$ to each of the $2k$ constituents, indexed by (composite $a\in\{0,1\}$, slot $i$). Let $\Psi$ be the many-body wavefunction. Assume that exchanging the two identical constituents in slot $i$ multiplies $\Psi$ by $-1$ if they are fermions and by $+1$ if they are bosons:
--   $$\Psi(c\circ\tau_i)=\varepsilon_i\,\Psi(c),\qquad \varepsilon_i=\begin{cases}-1&\text{slot } i \text{ fermionic}\\ +1&\text{slot } i\text{ bosonic.}\end{cases}$$
--   Then exchanging all constituents of one composite simultaneously with those of the other multiplies $\Psi$ by $(-1)^{N_F}$, where $N_F$ is the number of fermions in each composite:
--   $$\Psi(c\circ\sigma)=(-1)^{N_F}\,\Psi(c)\qquad\text{for all } c.$$
-- source:
--   Wikipedia, "Spin–statistics theorem" (https://en.wikipedia.org/wiki/Spin%E2%80%93statistics_theorem), PDF snapshot supplied by the proposal owner; section 'Composite particles', p. 4, first paragraph (sentences 2–3)

import Mathlib
import Definitions.Def_SpinStatistics_Defs

namespace SpinStatistics

theorem composite_exchange_sign {X : Type*} {k : ℕ} (fermion : Fin k → Prop)
    [DecidablePred fermion] (Ψ : (Fin 2 × Fin k → X) → ℂ)
    (hexch : ∀ i c, Ψ (c ∘ swapConstituent i) = (if fermion i then -1 else 1) * Ψ c) :
    ∀ c, Ψ (c ∘ swapComposites) =
      (-1) ^ (Finset.univ.filter fermion).card * Ψ c := by sorry

end SpinStatistics
