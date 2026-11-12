-- Prove2me | Theorems.Thm_QSampVerif_lemma_13_11
-- name    : QSampVerif.lemma_13_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:28:22.36321+00:00
-- url     : https://prove2.me/theorems/f058e2c8-f3e4-44ed-b11e-0d231519f9b7
-- title:
--   Lemma 13.11 — balanced operator polarization, $\sum_z\mu(B_z)=2\sqrt{\mu_i\mu_j}$
-- statement:
--   Let $\Omega$ be a positive semidefinite operator on a finite-dimensional space and $\mu(A)=\mathrm{Tr}(A\Omega A^\dagger)$. Let $A_i,A_j$ be operators with common input and output spaces with $\mu_i=\mu(A_i)>0$ and $\mu_j=\mu(A_j)>0$, let $\alpha=(\mu_j/\mu_i)^{1/4}$ and
--
--   $$B_z=\frac{\alpha A_i+z\alpha^{-1}A_j}{2}\qquad(z\in\mathcal Z=\{1,i,-1,-i\}).$$
--
--   Then for every operator $X$ on the input space
--
--   $$A_iXA_j^\dagger=\sum_{z\in\mathcal Z}z\,B_zXB_z^\dagger\qquad\text{and}\qquad\sum_{z\in\mathcal Z}\mu(B_z)=2\sqrt{\mu_i\mu_j}.\qquad(477)$$
--
--   The balancing factor $\alpha$ makes the total reference mass of the polarized operators the geometric mean of the two masses, which is what the cross-term bound (478) needs.
--
--   **Formalization Note** $\mu$ is the real part of the trace, which is the trace itself for positive semidefinite $\Omega$.
--
--   Differences from the source:
--   - generalization: Ω the reference state (a density operator) of §13.8 → any positive semidefinite Ω; reason: both identities use only that µ is real and nonnegative; a density operator is positive semidefinite, so the statement specializes to the printed one
--   - encoding: µ(A) = Tr(AΩA†); 𝒵 → the real part of the trace (refMass); z ranging over i^k, k ∈ Fin 4; reason: the trace is real for positive semidefinite Ω; same objects
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 13.11, (477), p.178 (PDF 179); µ and Ω, p.175 (PDF 176)

import Definitions.Def_QSampVerif_zPhase
import Definitions.Def_QSampVerif_refMass

set_option autoImplicit false

namespace QSampVerif

open scoped Matrix ComplexOrder

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Lemma 13.11 (Balanced operator polarization), (477), p.178 (PDF 179).

For operators `A_i, A_j` with common input and output spaces with `µ_i = µ(A_i) > 0` and
`µ_j = µ(A_j) > 0`, let `α = (µ_j/µ_i)^{1/4}` and `B_z = (α A_i + z α^{−1} A_j)/2`. Then for every
operator `X` on the input space, `A_i X A_j† = Σ_{z ∈ Z} z B_z X B_z†`, and
`Σ_{z ∈ Z} µ(B_z) = 2√(µ_i µ_j)`.

**Formalization Note.** `µ(A) = Tr(A Ω A†)` (`refMass`); the reference `Ω` is any positive
semidefinite operator on the input space (the paper's `Ω` is a density operator). -/
theorem lemma_13_11 {ι κ : Type*} [Fintype ι] [Fintype κ] (Ω : Matrix ι ι ℂ) (hΩ : Ω.PosSemidef)
    (Ai Aj : Matrix κ ι ℂ) (hi : 0 < refMass Ω Ai) (hj : 0 < refMass Ω Aj)
    (X : Matrix ι ι ℂ) :
    Ai * X * Ajᴴ = ∑ k : Fin 4, zPhase k •
      (((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj)) * X *
        ((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj))ᴴ) ∧
    ∑ k : Fin 4, refMass Ω
      ((2⁻¹ : ℂ) • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ) : ℝ) : ℂ) • Ai +
          zPhase k • ((((refMass Ω Aj / refMass Ω Ai) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) • Aj)) =
      2 * Real.sqrt (refMass Ω Ai * refMass Ω Aj) := by sorry

end QSampVerif
