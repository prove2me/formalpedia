-- Prove2me | Theorems.Thm_QuantumMC_Cooling_chiSq_gibbs_le
-- name    : QuantumMC.Cooling.chiSq_gibbs_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:43.004707+00:00
-- url     : https://prove2.me/theorems/303d0955-faf0-4c3d-9960-87664d3c9222
-- title:
--   §3.2, p. 17 — along a B-Chebyshev cooling schedule, χ²(π_{i+1}, π_i) ≤ B − 1 for all i
-- statement:
--   Let $\Omega$ be finite, $H:\Omega\to\mathbb N$ a Hamiltonian with at least one configuration of energy $0$, and let $0=\beta_0<\dots<\beta_\ell=\infty$ be a $B$-Chebyshev cooling schedule for the partition function $Z$ of $H$ (Definition 1). Then for every $i\in\{0,\dots,\ell-1\}$,
--   $$\chi^2(\pi_{i+1},\pi_i)\le B-1.$$
--
--   This turns the cooling-schedule condition into a divergence bound between consecutive Gibbs distributions.
--
--   **Formalization Note** The hypothesis that some $x$ has $H(x)=0$ (so $Z(\infty)>0$) is added and disclosed; the bound $H\le n$ is not needed and is omitted.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §3.2, p. 17, first sentence

import Mathlib
import Definitions.Def_QuantumMC_Cooling_Setting

open scoped ENNReal InnerProductSpace

namespace QuantumMC.Cooling

/-- §3.2, p. 17: if the `β_i` form a `B`-Chebyshev cooling schedule, then
`χ²(π_{i+1}, π_i) ≤ B - 1` for all `i < ℓ`. -/
theorem chiSq_gibbs_le {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (hZ : ∃ x, H x = 0)
    (β : ℕ → ℝ≥0∞) (ℓ : ℕ) (B : ℝ) (hsched : IsChebyshevSchedule H β ℓ B) :
    ∀ i < ℓ, chiSq (gibbs H (β (i + 1))) (gibbs H (β i)) ≤ B - 1 := by sorry

end QuantumMC.Cooling
