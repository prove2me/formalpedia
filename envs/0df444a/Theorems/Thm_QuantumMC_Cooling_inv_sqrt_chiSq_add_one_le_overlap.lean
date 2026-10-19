-- Prove2me | Theorems.Thm_QuantumMC_Cooling_inv_sqrt_chiSq_add_one_le_overlap
-- name    : QuantumMC.Cooling.inv_sqrt_chiSq_add_one_le_overlap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:52.113576+00:00
-- url     : https://prove2.me/theorems/e0bf2466-66da-4dd0-8e2b-64e5e9493e1d
-- title:
--   §3.2, p. 17 — 1/√(χ²(ν, π) + 1) ≤ Σ_x ν(x)√(π(x)/ν(x)) = ⟨ν|π⟩
-- statement:
--   Let $\nu$ and $\pi$ be probability distributions on a finite set $\Omega$, with $\pi(x)>0$ for every $x$. Then
--   $$\frac{1}{\sqrt{\chi^2(\nu,\pi)+1}}\le\sum_{x\in\Omega}\nu(x)\sqrt{\frac{\pi(x)}{\nu(x)}}=\langle\nu|\pi\rangle,$$
--   where $|\nu\rangle=\sum_x\sqrt{\nu(x)}|x\rangle$ and $|\pi\rangle=\sum_x\sqrt{\pi(x)}|x\rangle$ are the quantum sample states and $\langle\nu|\pi\rangle$ is their (complex) inner product. Terms with $\nu(x)=0$ contribute $0$ to the middle sum.
--
--   Combined with a bound on $\chi^2$, this gives a lower bound on the overlap of quantum samples.
--
--   **Formalization Note** The positivity of $\pi$ is implicit on the page (the display divides by $\pi(x)$) and is stated as a hypothesis. In Lean, $\nu(x)\sqrt{\pi(x)/\nu(x)}$ evaluates to $0$ when $\nu(x)=0$, which matches the sum over the support of $\nu$. The equality with $\langle\nu|\pi\rangle$ is stated in $\mathbb C$.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §3.2, p. 17, display after the first sentence

import Mathlib
import Definitions.Def_QuantumMC_Cooling_Setting

open scoped ENNReal InnerProductSpace

namespace QuantumMC.Cooling

/-- §3.2, p. 17 (Jensen display): for probability distributions `ν ≥ 0` and `π > 0` on `Ω`,
`1/√(χ²(ν, π) + 1) ≤ ∑_x ν(x) √(π(x)/ν(x)) = ⟨ν|π⟩`. -/
theorem inv_sqrt_chiSq_add_one_le_overlap {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν0 : ∀ x, 0 ≤ ν x) (hν : ∑ x, ν x = 1) (hπpos : ∀ x, 0 < π x) (hπ : ∑ x, π x = 1) :
    1 / Real.sqrt (chiSq ν π + 1) ≤ ∑ x, ν x * Real.sqrt (π x / ν x) ∧
      ((∑ x, ν x * Real.sqrt (π x / ν x) : ℝ) : ℂ) = ⟪qsample ν, qsample π⟫_ℂ := by sorry

end QuantumMC.Cooling
