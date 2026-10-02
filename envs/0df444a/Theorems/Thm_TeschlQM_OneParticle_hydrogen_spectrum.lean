-- Prove2me | Theorems.Thm_TeschlQM_OneParticle_hydrogen_spectrum
-- name    : TeschlQM.OneParticle.hydrogen_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:18:03.311305+00:00
-- url     : https://prove2.me/theorems/8d06f4e8-6ef8-4abf-818d-d88175b0f2d7
-- title:
--   Corollary 10.4 — the hydrogen atom has infinitely many negative eigenvalues accumulating at 0
-- statement:
--   Let $\gamma > 0$ and $H^{(1)} = -\Delta - \gamma/|x|$ on $L^2(\mathbb R^3)$. Then there is a sequence $E_0 < E_1 < E_2 < \dots < 0$ with $\lim_{j\to\infty} E_j = 0$ such that
--   $$\sigma_p(H^{(1)}) = \sigma_d(H^{(1)}) = \{E_j\}_{j \in \mathbb N_0}.$$
--
--   Together with $\sigma_{ess}(H^{(1)}) = [0,\infty)$ this gives the qualitative picture of the hydrogen spectrum: infinitely many bound states below zero, accumulating only at the threshold of the continuum.
--
--   **Formalization Note.** The book writes the set as $\{E_{j-1}\}_{j \in \mathbb N_0}$, an index slip; the eigenvalues are $E_0, E_1, \dots$, formalized as a strictly increasing `E : ℕ → ℝ` with negative values and limit $0$, whose range (in $\mathbb C$) equals both the point spectrum and the discrete spectrum.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 223, Corollary 10.4

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_hydrogenHamiltonian

namespace TeschlQM.OneParticle

open Filter Topology

/-- Teschl, Corollary 10.4, p. 223. Suppose `γ > 0`. Then
`σ_p(H⁽¹⁾) = σ_d(H⁽¹⁾) = {E_{j-1}}_{j∈ℕ}`, `E₀ < E_j < E_{j+1} < 0` (10.14), with
`lim_{j→∞} E_j = 0`. The book indexes the set by `j ∈ ℕ₀`, which would include `E_{-1}`; the
eigenvalues are `E₀, E₁, E₂, …`, a strictly increasing sequence of negative numbers. -/
theorem hydrogen_spectrum (γ : ℝ) (hγ : 0 < γ) :
    ∃ E : ℕ → ℝ, StrictMono E ∧ (∀ j, E j < 0) ∧ Tendsto E atTop (𝓝 0) ∧
      pointSpectrum (hydrogenHamiltonian γ) = Set.range (fun j => (E j : ℂ)) ∧
      discreteSpectrum (hydrogenHamiltonian γ) = Set.range (fun j => (E j : ℂ)) := by sorry

end TeschlQM.OneParticle
