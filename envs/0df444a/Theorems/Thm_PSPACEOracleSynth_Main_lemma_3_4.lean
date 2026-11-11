-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_3_4
-- name    : PSPACEOracleSynth.Main.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:16.627682+00:00
-- url     : https://prove2.me/theorems/bced662c-3a00-4a26-800e-479604747049
-- title:
--   Lemma 3.4 — moments of sums of $2\nu$-wise independent signs
-- statement:
--   Let $\nu\ge1$ be an integer and let $(\xi_i)_{i\in I}$ be finitely many $2\nu$-wise independent unbiased signs.
--
--   1. If $\alpha_i\in\mathbb C$ and $\sum_i|\alpha_i|^2\le\tau$, then
--   $$\mathbb E\Bigl|\sum_i\xi_i\alpha_i\Bigr|^{2\nu}\le(4\nu\tau)^\nu.$$
--   2. If $\Theta_i$ are Hermitian $d\times d$ matrices and $\sum_i\Theta_i^2\preceq\tau I$, then
--   $$\mathbb E\operatorname{Tr}\Bigl(\sum_i\xi_i\Theta_i\Bigr)^{2\nu}\le d\,(4\nu\tau)^\nu.$$
--
--   These moment bounds, valid already for limited independence, are what lets a search over polynomial-length seeds replace random signs in the construction of the contractive trailing block (Lemma 3.3).
--
--   **Formalization Note.** The signs are given by their joint law $p$ on $\{0,1\}^I$ (`IsKWiseUniform (2ν) p`), $\xi_i=(-1)^{\omega_i}$, and $\mathbb E F=\sum_\omega p(\omega)F(\omega)$. In item 2 the trace of the Hermitian matrix $X^{2\nu}$ is real and is taken as the real part of `Matrix.trace`.
--
--   Differences from the source:
--   - encoding: random signs (ξ_i) on a probability space → their joint law p on I → Bool with ξ_i = (−1)^{ω_i}, expectation Σ_ω p(ω)F(ω); reason: both bounds depend only on the joint law
--   - encoding: Tr(Σ ξ_i Θ_i)^{2ν} (a real number) → real part of the trace; reason: the trace of a Hermitian matrix is real
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §3.2, Lemma 3.4, p. 17

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Signs

open scoped ComplexOrder

namespace PSPACEOracleSynth.Main

/-- **Lemma 3.4**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 17. Let `ν ≥ 1` and let `(ξ_i)_{i ∈ I}` be finitely many `2ν`-wise independent unbiased
signs, with joint law `p` (`ξ_i = sgn (ω i)`, `E[F] = Σ_ω p(ω) F(ω)`).

1. If `α_i ∈ ℂ` and `Σ_i |α_i|² ≤ τ`, then `E |Σ_i ξ_i α_i|^{2ν} ≤ (4ντ)^ν`.
2. If `Θ_i` are Hermitian `d × d` matrices and `Σ_i Θ_i² ⪯ τ I`, then
   `E Tr (Σ_i ξ_i Θ_i)^{2ν} ≤ d (4ντ)^ν`. -/
theorem lemma_3_4 (ν : ℕ) (hν : 1 ≤ ν) {I : Type} [Fintype I] [DecidableEq I]
    (p : (I → Bool) → ℝ) (hp : IsKWiseUniform (2 * ν) p) :
    (∀ (α : I → ℂ) (τ : ℝ), ∑ i, ‖α i‖ ^ 2 ≤ τ →
        ∑ ω, p ω * ‖∑ i, (sgn (ω i) : ℂ) * α i‖ ^ (2 * ν) ≤ (4 * ν * τ) ^ ν) ∧
    (∀ (d : ℕ) (Θ : I → Matrix (Fin d) (Fin d) ℂ) (τ : ℝ), (∀ i, (Θ i).IsHermitian) →
        ((τ : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - ∑ i, Θ i * Θ i).PosSemidef →
        ∑ ω, p ω * (Matrix.trace ((∑ i, (sgn (ω i) : ℂ) • Θ i) ^ (2 * ν))).re
          ≤ d * (4 * ν * τ) ^ ν) := by sorry

end PSPACEOracleSynth.Main
