-- Prove2me | Theorems.Thm_ScutaruFid_rule_R2
-- name    : ScutaruFid.rule_R2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:04.162001+00:00
-- url     : https://prove2.me/theorems/ab3346b1-9b77-49a7-839c-0835ac005741
-- title:
--   Rule R2, eqs. (6)–(9): the positive square root of a Gaussian density operator
-- statement:
--   Let $\rho$ be a density operator on $L^2(\mathbb R)$ with Gaussian kernel $\exp[-(ax^2+dy^2+2bxy)+lx+ky+g]$, where $g$ is real. Put $s=a+d-2b$ (a positive real number) and $-b\ge0$. Then the positive square root $\sqrt\rho$ is the integral operator with the Gaussian kernel
--
--   $$
--   \langle x|\sqrt\rho|y\rangle=\exp\big[-(\tilde ax^2+\tilde dy^2+2\tilde bxy)+\tilde lx+\tilde ky+\tilde g\big],
--   $$
--
--   whose parameters are
--
--   $$
--   \tilde a=a-b,\qquad \tilde d=d-b,\qquad \tilde b=-\sqrt{-b\,s}\ (\text{so }-\tilde b\ge0),
--   $$
--   $$
--   \tilde l+\tilde k=\frac{l+k}{1+2\sqrt{-b/s}},\qquad \tilde l-\tilde k=l-k,\qquad
--   \tilde g=\tfrac12g-\tfrac12\ln\sqrt{\frac{\pi}{s}}-\frac{(l+k)^2}{8(\sqrt s+2\sqrt{-b})^2}.
--   $$
--
--   Rule R2 gives the factors $\sqrt{\rho_1}$ in Uhlmann's fidelity explicitly inside the oscillator semigroup.
--
--   **Formalization Note** $\sqrt\rho$ is the positive square root `opSqrt ρ` (Mathlib's `CFC.sqrt`). The quantities $s$ and $-b$ are real for a density operator (`density_kernel_conditions`), and every square root above is the real square root of their real parts. $\tilde l$ and $\tilde k$ are written out from their sum and difference.
--
--   Differences from the source:
--   - reading: √ρ is the integral operator with Gaussian kernel (6) such that (7), with the sign chosen so that −b̃ ≥ 0 → √ρ is the positive square root opSqrt ρ (CFC.sqrt), whose kernel is (6) with (8)–(9); reason: fidelity (1) uses the positive root; the page's sign choice −b̃ ≥ 0 selects it (the root with b̃ > 0 also squares to ρ but is not positive)
--   - encoding: complex constant g → g real; reason: the kernel fixes g only modulo 2πi and e^g > 0, so every Gaussian density operator has a representation with g real, the page's convention; with complex g the factor ½g in (9) is ambiguous
--   - encoding: √(−b(a+d−2b)), √(−b/(a+d−2b)), √(a+d−2b), √(−b) → real square roots of the real parts of −b and a + d − 2b; reason: for a density operator these are nonnegative reals (density_kernel_conditions)
--   - encoding: l̃ + k̃ and l̃ − k̃ → l̃ and k̃ solved explicitly as half the sum and half the difference; reason: same values
--   - encoding: density operator → IsDensityOperator B ρ with the trace in an arbitrary Hilbert basis B; reason: the trace of a trace-class operator does not depend on the basis
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eqs. (6)–(9), p.2

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_gaussKernel
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_ScutaruFid_opSqrt

namespace ScutaruFid

/-- **Rule R2: the square root of a Gaussian density operator**, eqs. (6)–(9). Scutaru,
arXiv:quant-ph/9708013v1, eqs. (6)–(9), p.2: "We shall define the operator √ρ as the integral
operator with the Gaussian kernel <x|√ρ|y> = exp[−(ãx² + d̃y² + 2b̃xy) + l̃x + k̃y + g̃] (6) such
that <x|ρ|y> = ∫ <x|√ρ|z><z|√ρ|y> dz (7) … ã = a − b, d̃ = d − b, b̃ = −√(−b(a + d − 2b)) (8)
where the minus sign was choosen in order to have −b̃ ≥ 0. Also l̃ + k̃ = (l + k)/(1 + 2√(−b/(a+d−2b))),
l̃ − k̃ = l − k, g̃ = ½g − ½ ln √(π/(a + d − 2b)) − (l + k)²/(8(√(a + d − 2b) + 2√(−b))²) (9)".

If `ρ` is a density operator on `L²(ℝ)` with Gaussian kernel (3) whose constant `g` is real, then
its positive square root `√ρ` is the integral operator with the Gaussian kernel (6) whose
parameters are (8)–(9), with the sign `b̃ = −√(−b(a + d − 2b)) ≤ 0`.
With `s = a + d − 2b` and `r = √(−b/s)`, the linear coefficients are `l̃ = ((l + k)/(1 + 2r) + (l − k))/2`, `k̃ = ((l + k)/(1 + 2r) − (l − k))/2`.

**Formalization Note** `√ρ` is `opSqrt ρ` (Mathlib's `CFC.sqrt`), the positive square root used
in the fidelity (1); the page defines √ρ as the Gaussian kernel operator with (7) and the sign
choice `−b̃ ≥ 0`, which selects exactly this root (the root with `b̃ > 0` also squares to `ρ` but
is not positive). The quantities `s = a + d − 2b` and `−b` are real for a density
operator (`density_kernel_conditions`), and every square root in (8)–(9) is the real square root
of their real parts. `g` is taken real, the page's convention; every Gaussian density operator has
such a representation (the kernel fixes `g` only modulo `2πi`, and `exp g > 0`). -/
theorem rule_R2 {ι : Type*} (B : HilbertBasis ι ℂ L2R) (ρ : L2R →L[ℂ] L2R) (a b d l k : ℂ)
    (g : ℝ) (hρ : IsDensityOperator B ρ) (hK : IsKernelOperator ρ (gaussKernel a b d l k g)) :
    let s : ℝ := (a + d - 2 * b).re
    let nb : ℝ := -b.re
    let r : ℝ := Real.sqrt (nb / s)
    let bt : ℝ := -Real.sqrt (nb * s)
    let lk : ℂ := (l + k) / (1 + 2 * (r : ℂ))
    IsKernelOperator (opSqrt ρ)
        (gaussKernel (a - b) (bt : ℂ) (d - b) ((lk + (l - k)) / 2) ((lk - (l - k)) / 2)
          ((1 / 2 : ℂ) * (g : ℂ) - (1 / 2 : ℂ) * ((Real.log (Real.sqrt (Real.pi / s)) : ℝ) : ℂ) -
            (l + k) ^ 2 / (8 * ((Real.sqrt s + 2 * Real.sqrt nb : ℝ) : ℂ) ^ 2))) := by sorry

end ScutaruFid
