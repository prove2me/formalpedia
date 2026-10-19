-- Prove2me | Theorems.Thm_QuantumMC_Cooling_chiSq_eq_sum_sq_div_sub_one
-- name    : QuantumMC.Cooling.chiSq_eq_sum_sq_div_sub_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:35.704608+00:00
-- url     : https://prove2.me/theorems/17dddf58-748d-454d-91ea-c218677203b7
-- title:
--   §3.2, p. 16 — χ²(ν, π) = Σ_x ν(x)²/π(x) − 1
-- statement:
--   Let $\nu$ and $\pi$ be functions on a finite set $\Omega$ with $\sum_x\nu(x)=1$, $\sum_x\pi(x)=1$ and $\pi(x)>0$ for every $x$. Then the chi-squared divergence has the second form
--   $$\chi^2(\nu,\pi)=\sum_{x\in\Omega}\pi(x)\Big(\frac{\nu(x)}{\pi(x)}-1\Big)^2=\sum_{x\in\Omega}\frac{\nu(x)^2}{\pi(x)}-1.$$
--
--   This is the form in which the paper evaluates $\chi^2$ between consecutive Gibbs distributions.
--
--   **Formalization Note** The positivity of $\pi$ is implicit on the page, which divides by $\pi(x)$; it is stated as a hypothesis.
-- source:
--   Montanaro, Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, §3.2, p. 16, display defining χ²

import Mathlib
import Definitions.Def_QuantumMC_Cooling_Setting

open scoped ENNReal InnerProductSpace

namespace QuantumMC.Cooling

/-- §3.2, p. 16: for probability vectors `ν, π` on `Ω` with `π > 0`,
`χ²(ν, π) = ∑_x π(x)(ν(x)/π(x) - 1)² = ∑_x ν(x)²/π(x) - 1`. -/
theorem chiSq_eq_sum_sq_div_sub_one {Ω : Type*} [Fintype Ω] (ν π : Ω → ℝ)
    (hν : ∑ x, ν x = 1) (hπ : ∑ x, π x = 1) (hπpos : ∀ x, 0 < π x) :
    chiSq ν π = ∑ x, ν x ^ 2 / π x - 1 := by sorry

end QuantumMC.Cooling
