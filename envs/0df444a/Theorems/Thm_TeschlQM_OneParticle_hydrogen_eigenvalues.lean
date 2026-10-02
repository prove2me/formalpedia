-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_hydrogen_eigenvalues
-- name    : TeschlQM.OneParticle.hydrogen_eigenvalues
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:24:53.833824+00:00
-- url     : https://prove2.me/theorems/9ccc5547-6eb2-41c5-9ee8-6d7dfb1f28e8
-- title:
--   Theorem 10.9 (eigenvalues) — E_n = −(γ/(2(n+1)))² for the hydrogen atom
-- statement:
--   Let $\gamma > 0$ and $H^{(1)} = -\Delta - \gamma/|x|$ on $L^2(\mathbb R^3)$. The eigenvalues of $H^{(1)}$ are explicitly given by
--   $$E_n = -\left(\frac{\gamma}{2(n+1)}\right)^2, \qquad n \in \mathbb N_0 .$$
--
--   These are the Bohr energy levels of the hydrogen atom in units $\hbar = 1$, $m = 1/2$, derived here from the Schrödinger operator rather than from the Bohr model.
--
--   **Formalization Note.** Only the eigenvalue part (10.63) of Theorem 10.9 is formalized: the point spectrum of `hydrogenHamiltonian γ` equals $\{E_n : n \in \mathbb N\}$ as a subset of $\mathbb C$. The explicit orthonormal eigenbasis (10.64)–(10.65) is not part of the statement.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 231, Theorem 10.9, Eq. (10.63)

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_hydrogenHamiltonian

namespace TeschlQM.OneParticle

/-- Teschl, Theorem 10.9, p. 231 (eigenvalue part). For the Coulomb potential with `γ > 0`
(10.57), the eigenvalues of `H⁽¹⁾` are explicitly given by `E_n = -(γ / (2(n + 1)))²`,
`n ∈ ℕ₀` (10.63). -/
theorem hydrogen_eigenvalues (γ : ℝ) (hγ : 0 < γ) :
    pointSpectrum (hydrogenHamiltonian γ) =
      Set.range (fun k : ℕ => ((-((γ / (2 * ((k : ℝ) + 1))) ^ 2) : ℝ) : ℂ)) := by sorry

end TeschlQM.OneParticle
