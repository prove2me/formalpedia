-- Prove2me | Theorems.Thm_QRHLittlewood_pl_exact
-- name    : QRHLittlewood.pl_exact
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T15:43:55.932957+00:00
-- url     : https://prove2.me/theorems/2ccb82a3-3a06-4b6e-bc03-1887ceab7e6e
-- title:
--   Lossless Phragmén–Lindelöf bound with a linear edge growth
-- statement:
--   Let $f$ be an entire function and $C,A>0$. Assume:
--
--   1. $|f(s)|\le C\,A\,|1+s|$ on the line $\Re s=-\tfrac12$;
--   2. $|f(s)|\le C$ on the line $\Re s=\tfrac32$;
--   3. $f$ has at most exponential growth on the strip: $|f(s)|\le B\,e^{\kappa|\Im s|}$ for $-\tfrac12\le\Re s\le\tfrac32$, for some constants $B,\kappa$.
--
--   Then for every $s$ with $-\tfrac12\le\Re s\le\tfrac32$,
--
--   $$|f(s)|\le C\,\bigl(A\,|1+s|\bigr)^{(3/2-\Re s)/2}.$$
--
--   This is Rademacher's convexity principle without any loss in the constant. Applied to $L(s,\chi)$ with $C=\zeta(3/2)$ and $A=q/(2\pi)$, it gives the exact convexity bound for primitive Dirichlet $L$-functions.
-- source:
--   H. Rademacher, On the Phragmén–Lindelöf theorem and some applications, Math. Z. 72 (1959/60), 192–204; B. W. Daugherty, S. Ryan, G. Ward, Certified harmonic-measure barriers and explicit Littlewood bounds from zero-free regions, https://doi.org/10.5281/zenodo.23400116, Section 6 (Dirichlet inputs)

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Complex

namespace QRHLittlewood

theorem pl_exact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C A : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖f s‖ ≤ C * (A * ‖1 + s‖))
    (hright : ∀ s : ℂ, s.re = 3 / 2 → ‖f s‖ ≤ C)
    (hgrowth : ∃ B κ : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖f s‖ ≤ B * Real.exp (κ * |s.im|))
    (s₁ : ℂ) (h₁ : -1 / 2 ≤ s₁.re) (h₂ : s₁.re ≤ 3 / 2) :
    ‖f s₁‖ ≤ C * (A * ‖1 + s₁‖) ^ ((3 / 2 - s₁.re) / 2) := by sorry

end QRHLittlewood
