-- Prove2me | Theorems.Thm_QuantumMC_Cooling_overlap_ge_inv_B
-- name    : QuantumMC.Cooling.overlap_ge_inv_B
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:27:03.469852+00:00
-- url     : https://prove2.me/theorems/eacdd634-96fd-49a9-ae9c-b4aec0557c35
-- title:
--   §3.2, p. 17 — along a B-Chebyshev cooling schedule, |⟨π_i|π_{i+1}⟩|² ≥ 1/B for all i
-- statement:
--   Let $\Omega$ be a finite set of configurations and $H:\Omega\to\{0,1,\dots,n\}$ a Hamiltonian with at least one configuration of energy $0$. Let $Z(\beta)=\sum_{x}e^{-\beta H(x)}$ be its partition function and let $0=\beta_0<\beta_1<\dots<\beta_\ell=\infty$ be a $B$-Chebyshev cooling schedule for $Z$ (Definition 1). For each $i$ let $\pi_i(x)=e^{-\beta_iH(x)}/Z(\beta_i)$ be the Gibbs distribution and $|\pi_i\rangle=\sum_x\sqrt{\pi_i(x)}|x\rangle$ its quantum sample state. Then for every $i\in\{0,\dots,\ell-1\}$,
--   $$|\langle\pi_i|\pi_{i+1}\rangle|^2\ge\frac1B.$$
--
--   This is the overlap condition required by the Wocjan–Abeyesinghe quantum sampling theorem (Theorem 9 of the paper, with $p=1/B$): it says that each Gibbs state in a Chebyshev cooling schedule is close enough to its predecessor for quantum walks to prepare it from the previous one, and it is what the paper's partition-function algorithm (Theorem 11) uses.
--
--   **Formalization Note** Inverse temperatures are in $[0,\infty]$ with $e^{-\infty\cdot h}=[h=0]$. The hypothesis that some configuration has $H(x)=0$ is added and disclosed: it makes $Z(\infty)>0$, without which $\pi_\ell$ and the last ratio of Definition 1 would be divisions by zero. No hypothesis on $B$ is made; Definition 1 forces $B\ge1$. The hypothesis $H\le n$ is the paper's model and is kept although the claim does not use it.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §3.2, p. 17, sentence "So, for all i, |⟨π_i|π_{i+1}⟩|² ≥ 1/B."

import Mathlib
import Definitions.Def_QuantumMC_Cooling_Setting

open scoped ENNReal InnerProductSpace

namespace QuantumMC.Cooling

/-- §3.2, p. 17: along a `B`-Chebyshev cooling schedule `0 = β_0 < ⋯ < β_ℓ = ∞` for the
partition function of a Hamiltonian `H : Ω → {0, …, n}`, the quantum sample states of
consecutive Gibbs distributions satisfy `|⟨π_i|π_{i+1}⟩|² ≥ 1/B` for all `i < ℓ`. -/
theorem overlap_ge_inv_B {Ω : Type*} [Fintype Ω] (H : Ω → ℕ) (n : ℕ) (hH : ∀ x, H x ≤ n)
    (hZ : ∃ x, H x = 0) (β : ℕ → ℝ≥0∞) (ℓ : ℕ) (B : ℝ)
    (hsched : IsChebyshevSchedule H β ℓ B) :
    ∀ i < ℓ,
      1 / B ≤ ‖⟪qsample (gibbs H (β i)), qsample (gibbs H (β (i + 1)))⟫_ℂ‖ ^ 2 := by sorry

end QuantumMC.Cooling
