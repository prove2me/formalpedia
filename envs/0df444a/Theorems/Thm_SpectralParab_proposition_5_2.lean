-- Prove2me | Theorems.Thm_SpectralParab_proposition_5_2
-- name    : SpectralParab.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:08.118676+00:00
-- url     : https://prove2.me/theorems/3c39414e-b08d-410e-9d21-a39480998d31
-- title:
--   Proposition 5.2: characterization of parabolic regularity (corrected: (b) does not imply (a) or (c))
-- statement:
--   Let $\mathbf X$ be a finite-dimensional Hilbert space, $f:\mathbf X\to\overline{\mathbb R}$ convex and finite at $\bar x$, and $\bar v\in\partial f(\bar x)$. Consider:
--
--   1. (a) $f$ is parabolically regular at $\bar x$ for $\bar v$;
--   2. (b) for every $w\in K_f(\bar x,\bar v)$, $\displaystyle \mathrm d^2f(\bar x,\bar v)(w)=\inf_{z\in\mathbf X}\{\mathrm d^2f(\bar x)(w\,|\,z)-\langle z,\bar v\rangle\}$;
--   3. (c) for every $w\in\operatorname{dom}\mathrm d^2f(\bar x,\bar v)$ there is $\bar z\in\operatorname{dom}\mathrm d^2f(\bar x)(w\,|\,\cdot)$ with $\mathrm d^2f(\bar x,\bar v)(w)=\mathrm d^2f(\bar x)(w\,|\,\bar z)-\langle\bar z,\bar v\rangle$.
--
--   Then (a) $\Leftrightarrow$ (c), and (a) $\Rightarrow$ (b).
--
--   The page states (a), (b), (c) equivalent; the implications from (b) are false (see below), so this item states the corrected equivalence. Parabolic regularity is thus the attainment, in (c), of the infimum in (b).
--
--   **Formalization Note** The infimum is taken in `EReal`, over all of $\mathbf X$; $\langle z,\bar v\rangle$ is a real number, so no $\infty-\infty$ occurs. Finiteness of $f(\bar x)$ is part of the Lean subdifferential.
--
--   Differences from the source:
--   - correction: (a), (b) and (c) are equivalent → (a) ⇔ (c), and (a) ⇒ (b); reason: (b) ⇒ (a) and (b) ⇒ (c) are false: f(x,y) = x² + x⁴/y for y > 0, f(0,0) = 0, +∞ otherwise, is convex and lsc, 0 ∈ ∂f(0); (b) holds at every w ∈ K_f(0,0) = {y ≥ 0}, but at w = (1,0) d²f(0,0)(w) = 2 while d²f(0)(w|z) = 2 + 4/z₂ (z₂ > 0), so the infimum is not attained ((c) fails) and every w_k with ‖w_k − w‖ ≤ Ct_k has quotients ≥ 2 + 2/C − o(1) ((a) fails)
--   - encoding: X a finite-dimensional Hilbert space (standing assumption, p.3) → E a real inner-product space with [FiniteDimensional ℝ E]; reason: the standing assumption of §2 written as a typeclass; same instances
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: f finite at x̄, a separate assumption → no separate binder; finiteness of f(x̄) is a conjunct of v̄ ∈ subdiff f x̄; reason: v̄ ∈ ∂f(x̄) already supplies it; same instances
--   - encoding: Definition 5.1 is stated for a convex f and v̄ ∈ ∂f(x̄) → ParabRegularAt carries neither condition; ParabRegular quantifies over v̄ ∈ subdiff; reason: here both are hypotheses of the item, so nothing changes
--   - encoding: lim sup_k ‖w_k − w‖/t_k < ∞ → ∃ C, ∀ k, ‖w_k − w‖ ≤ C t_k; reason: equivalent because t_k > 0
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 5.2, p.22

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 5.2, p.22 (characterization of parabolic regularity, cited
from [24, Proposition 3.6]), **corrected**. Let `f : X → R̄` be convex on a finite-dimensional
Hilbert space, finite at `x̄`, and `v̄ ∈ ∂f(x̄)`. Consider
(a) `f` is parabolically regular at `x̄` for `v̄`;
(b) for every `w ∈ K_f(x̄, v̄)`, `d²f(x̄, v̄)(w) = inf_{z} {d²f(x̄)(w | z) − ⟨z, v̄⟩}`;
(c) for every `w ∈ dom d²f(x̄, v̄)` there is `z̄ ∈ dom d²f(x̄)(w | ·)` with
`d²f(x̄, v̄)(w) = d²f(x̄)(w | z̄) − ⟨z̄, v̄⟩`.
Then (a) ⇔ (c), and (a) ⇒ (b).
**Formalization Note.** The page claims (a), (b), (c) equivalent; (b) ⇒ (a) and (b) ⇒ (c) are false
(counterexample: `f(x, y) = x² + x⁴/y` for `y > 0`, `f(0,0) = 0`, `+∞` otherwise, at `x̄ = 0`,
`v̄ = 0`, `w = (1, 0)`), so this item states the corrected implications. `FiniteDimensional` is
the standing assumption of p.3. Finiteness of `f(x̄)` is a conjunct of `v̄ ∈ subdiff f x̄`. The infimum is taken in `EReal`. -/
theorem proposition_5_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (hconv : IsConvexFn f) (xbar : E) (vbar : E) (hv : vbar ∈ subdiff f xbar) :
    (ParabRegularAt f xbar vbar ↔
      ∀ w, secondSubderiv f xbar vbar w < ⊤ →
        ∃ zbar, parabSubderiv f xbar w zbar < ⊤ ∧
          secondSubderiv f xbar vbar w = parabSubderiv f xbar w zbar - ((⟪zbar, vbar⟫ : ℝ) : EReal)) ∧
    (ParabRegularAt f xbar vbar →
      ∀ w ∈ critCone f xbar vbar,
        secondSubderiv f xbar vbar w = ⨅ z : E, (parabSubderiv f xbar w z - ((⟪z, vbar⟫ : ℝ) : EReal))) := by sorry

end SpectralParab
