-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_lemma_12
-- name    : ShadowTomography.UpperBound.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:05:14.560003+00:00
-- url     : https://prove2.me/theorems/f45c2bbe-2f52-4636-b100-df3bb8b08783
-- title:
--   Lemma 12 (Quantum Union Bound), probability part — M measurements each accepting w.p. ≥ 1 − ε all accept w.p. ≥ 1 − 2M√ε
-- statement:
--   Let $\rho$ be a mixed state and $E_1,\dots,E_M$ two-outcome measurements with $\mathrm{Tr}(E_i\rho)\ge 1-\varepsilon$ for all $i\in[M]$. If $E_1,\dots,E_M$ are applied to $\rho$ in succession, the probability that they all accept is at least
--
--   $$
--   1-2M\sqrt{\varepsilon}.
--   $$
--
--   The Quantum Union Bound controls the damage done by a long sequence of measurements, each individually likely to accept; in the proof of Theorem 2 it bounds the probability that some postselection step rejects the true amplified state.
--
--   **Formalization Note** Only the probability part of Lemma 12 is formalized. The printed lemma also asserts that, conditioned on acceptance, a post-measurement state $\tilde\rho$ with $\|\tilde\rho-\rho\|_{\mathrm{tr}}=O(\sqrt{M\varepsilon})$ can be recovered; that part has an unquantified $O(\cdot)$ and is not stated here. "Applied in succession" is implemented with Lüders instruments (Kraus operator $\sqrt{E_i}$ on acceptance) in the order $E_1, E_2,\dots$; the paper does not fix the instrument. `Real.sqrt` of a negative number is $0$, which only matters when no hypothesis can hold ($\varepsilon<0$ forces $M=0$).
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 13, Lemma 12 (probability part)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_seqAccept

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Lemma 12 (Quantum Union Bound), probability part.** If two-outcome measurements
`E 0, …, E (M-1)` each accept the state `ρ` with probability at least `1 - ε`, then applying them
to `ρ` in succession (in this order, each by its Lüders instrument), all of them accept with
probability at least `1 - 2M√ε`. -/
theorem lemma_12 {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) (ε : ℝ) (hE : ∀ i, IsEffect (E i)) (hρ : WildeQIT.IsDensityOperator ρ)
    (hacc : ∀ i, 1 - ε ≤ ((E i) * ρ).trace.re) :
    1 - 2 * M * Real.sqrt ε ≤ seqAccept E ρ := by sorry

end ShadowTomography.UpperBound
