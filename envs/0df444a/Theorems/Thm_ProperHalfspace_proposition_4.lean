-- Prove2me | Theorems.Thm_ProperHalfspace_proposition_4
-- name    : ProperHalfspace.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:02.062034+00:00
-- url     : https://prove2.me/theorems/d66d9dba-7db2-4019-8337-2e9f66774472
-- title:
--   Proposition 4 — Peres' noise-stability bound for halfspaces
-- statement:
--   Let $h(x)=\operatorname{sign}(w\cdot x-\theta)$ be a halfspace on $\{\pm1\}^n$ and let $\rho\in[0,1]$. Then
--   $$\|T_\rho h-h\|_{L^1(\{\pm1\}^n)}\le2\sqrt{2(1-\rho)}.$$
--
--   The bound does not depend on the dimension; it controls the cost of replacing a target by its smoothed version.
--
--   Differences from the source: none.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Proposition 4, p.13; cited from Peres 2004

import Mathlib
import Definitions.Def_ProperHalfspace_Halfspace
import Definitions.Def_ProperHalfspace_Fourier

namespace ProperHalfspace

/-- Proposition 4, p.13 (Peres' theorem, [Per04]). De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026).
`‖T_ρ h − h‖_{L¹({±1}ⁿ)} ≤ 2 √(2(1−ρ))` for every halfspace `h` and every `ρ ∈ [0, 1]`. -/
theorem proposition_4 {n : ℕ} (w : Fin n → ℝ) (θ ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    cubeAvg (fun x => |noiseOp ρ (ltf w θ) x - ltf w θ x|) ≤ 2 * Real.sqrt (2 * (1 - ρ)) := by sorry

end ProperHalfspace
