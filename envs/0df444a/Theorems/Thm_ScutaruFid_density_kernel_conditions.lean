-- Prove2me | Theorems.Thm_ScutaruFid_density_kernel_conditions
-- name    : ScutaruFid.density_kernel_conditions
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:59.792379+00:00
-- url     : https://prove2.me/theorems/1299b6c1-64c0-4cc9-bac2-957d57582d65
-- title:
--   Conditions for a Gaussian kernel to define a density operator (corrected: $e^g$ instead of $g=\bar g$; strict $\operatorname{Re}a+b>0$)
-- statement:
--   Let $\rho$ be a density operator on $L^2(\mathbb R)$ (trace class, positive, trace $1$) whose kernel is Gaussian:
--
--   $$
--   \langle x|\rho|y\rangle=\exp\big[-(ax^2+dy^2+2bxy)+lx+ky+g\big],\qquad a,b,d,l,k,g\in\mathbb C .
--   $$
--
--   Then
--
--   1. $d=\bar a$, $b\in\mathbb R$ and $k=\bar l$ (Hermiticity);
--   2. $\operatorname{Re}a+b>0$ and the constant is fixed by the trace:
--   $$
--   e^{g}=\exp\Big(-\frac{(\operatorname{Re}l)^2}{2(\operatorname{Re}a+b)}\Big)\sqrt{\frac{2(\operatorname{Re}a+b)}{\pi}},
--   $$
--   i.e. $g=-\frac{(\operatorname{Re}l)^2}{2(\operatorname{Re}a+b)}-\ln\sqrt{\frac{\pi}{2(\operatorname{Re}a+b)}}$ modulo $2\pi i$;
--   3. $-b\ge0$ (positivity). Hence $\operatorname{Re}a\ge-b\ge0$.
--
--   These are the constraints that make the six-parameter family (3) a family of quantum states; they are used to make sense of the real square roots in rule R2 and of the normalization of every state kernel in the mission.
--
--   Differences from the source:
--   - correction: Hermiticity requires g = ḡ, and g = −(Re l)²/(2(Re a+b)) − ln √(π/(2(Re a+b))) → the same formula for e^g (g is determined modulo 2πi); reason: exp is 2πi-periodic, so g and g + 2πi give the same kernel; the vacuum with g = −½ ln π + 2πi is a Hermitian density operator with ḡ ≠ g
--   - generalization: Re a ≥ −b → Re a + b > 0; reason: a stronger conclusion that implies the printed one; at Re a + b = 0 the page's own formula for g divides by zero and the operator is not trace class
--   - encoding: density operator, trace ρ = 1 → IsDensityOperator B ρ with the trace in an arbitrary Hilbert basis B; reason: the trace of a trace-class operator does not depend on the basis
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, p.1, paragraph after (3)

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_gaussKernel
import Definitions.Def_ScutaruFid_IsDensityOperator

namespace ScutaruFid

/-- **Density conditions on a Gaussian kernel** (corrected: `exp g` instead of `g = ḡ`; strict
`Re a + b > 0`). Scutaru, arXiv:quant-ph/9708013v1, p.1, paragraph after (3): "Hermiticity for ρ
requires d = ā, b = b̄, k = l̄ and g = ḡ [16]. From traceρ = 1 it follows that
g = −(Rel)²/(2(Rea+b)) − ln √(π/(2(Rea+b))) and Rea ≥ −b. From the non-negativity of <ψ|ρ|ψ> for
all |ψ> it follows [16] that −b ≥ 0. Hence Rea ≥ −b ≥ 0."

If a density operator `ρ` on `L²(ℝ)` (trace class, positive, trace `1` in the Hilbert basis `B`)
has the Gaussian kernel `exp[−(ax² + dy² + 2bxy) + lx + ky + g]`, then `d = ā`, `b` is real,
`k = l̄`, `Re a + b > 0`, `exp g = exp(−(Re l)²/(2(Re a + b))) · √(2(Re a + b)/π)` and `b ≤ 0`.

**Formalization Note** The page's `g = ḡ` holds only modulo `2πi` (the kernel determines `g`
only up to `2πi`), so the normalization is stated for `exp g`; it is the page's formula for `g`
exponentiated. The page's `Re a ≥ −b` is strengthened to `Re a + b > 0` (at `Re a + b = 0` the
page's own formula for `g` divides by zero, and the operator is not trace class). -/
theorem density_kernel_conditions {ι : Type*} (B : HilbertBasis ι ℂ L2R) (ρ : L2R →L[ℂ] L2R)
    (a b d l k g : ℂ) (hρ : IsDensityOperator B ρ)
    (hK : IsKernelOperator ρ (gaussKernel a b d l k g)) :
    d = star a ∧ b.im = 0 ∧ k = star l ∧ 0 < a.re + b.re ∧
      Complex.exp g = ((Real.exp (-(l.re ^ 2) / (2 * (a.re + b.re))) *
        Real.sqrt (2 * (a.re + b.re) / Real.pi) : ℝ) : ℂ) ∧
      b.re ≤ 0 := by sorry

end ScutaruFid
