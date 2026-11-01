-- Prove2me | Theorems.Thm_ScutaruFid_thermal_kernel
-- name    : ScutaruFid.thermal_kernel
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:59.780599+00:00
-- url     : https://prove2.me/theorems/ae5f2634-b4fb-49af-9e31-08ffa9f142b2
-- title:
--   Eq. (14): kernel of the thermal state (corrected: $\tanh(\beta/2)$ in the normalization)
-- statement:
--   Let $\beta>0$ and $\gamma=\coth(\beta/2)$. The kernel of the undisplaced, unsqueezed Gaussian state with matrix $A=\gamma I$ (the thermal state of the oscillator at inverse temperature $\beta$) is
--
--   $$
--   \langle x|\rho_1|y\rangle=\exp\Big[-\tfrac12\coth\beta\,(x^2+y^2)+\frac{xy}{\sinh\beta}-\ln\sqrt{\frac{\pi}{\tanh(\beta/2)}}\Big].
--   $$
--
--   This is the first state of the paper's computation of (17) after the reduction by F4.
--
--   Differences from the source:
--   - correction: − ln √(π/tanh β) → − ln √(π/tanh(β/2)); reason: the diagonal of the kernel is exp(−tanh(β/2) x²), so with the printed constant the trace is √(tanh β/tanh(β/2)) ≠ 1 (1.2838… at β = 1); the quadratic part is as printed
--   - reading: the thermal state ρ1 with parameter β → the state with kernel stateKernel (coth(β/2) I) 0, β > 0; reason: the page does not define β and describes a thermal state only as "an undisplaced and unsqueezed state"; the thermal state of the oscillator at inverse temperature β > 0 is the undisplaced Gaussian state with A = coth(β/2) I in the normalization of (11), and this is the β for which the quadratic part of (14) is as printed
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (14), p.2

import Mathlib
import Definitions.Def_ScutaruFid_stateKernel

namespace ScutaruFid

/-- **Kernel of the thermal state**, eq. (14) (corrected: `tanh(β/2)` in the normalization).
Scutaru, arXiv:quant-ph/9708013v1, eq. (14), p.2: "It is well known that in this case [14]:
<x|ρ1|y> = exp[−½ cothβ (x² + y²) + xy/sinhβ − ln √(π/tanhβ)]".

For `β > 0` and `γ = coth(β/2)`, the kernel of the undisplaced unsqueezed state with matrix
`γ I` is `exp[−½ coth β (x² + y²) + xy/sinh β − ln √(π/tanh(β/2))]`.

**Formalization Note** The thermal state of the oscillator at inverse temperature `β` is the
undisplaced Gaussian state with `A = coth(β/2) I` (in the normalization of (11), vacuum `A = I`).
The page prints `tanh β` in the normalization constant; the resulting kernel has trace
`√(tanh β / tanh(β/2)) ≠ 1` (`1.2838…` at `β = 1`), so `tanh(β/2)` is the correct constant. The
quadratic part is as printed. -/
theorem thermal_kernel (β : ℝ) (hβ : 0 < β) (x y : ℝ) :
    stateKernel (!![Real.cosh (β / 2) / Real.sinh (β / 2), 0; 0, Real.cosh (β / 2) / Real.sinh (β / 2)])
        0 x y =
      Complex.exp ((-(1 / 2) * (Real.cosh β / Real.sinh β) * (x ^ 2 + y ^ 2) + x * y / Real.sinh β -
        Real.log (Real.sqrt (Real.pi / Real.tanh (β / 2))) : ℝ) : ℂ) := by sorry

end ScutaruFid
