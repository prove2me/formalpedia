-- Prove2me | Theorems.Thm_SpectralParab_proposition_4_6
-- name    : SpectralParab.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:37.451988+00:00
-- url     : https://prove2.me/theorems/f54978f1-aae7-4850-8a38-8b955ce7f9b5
-- title:
--   Proposition 4.6: domains of $\mathrm df(\bar x)$ and $\mathrm d^2f(\bar x)(w|\cdot)$, and parabolic derivability of $\operatorname{dom}f$
-- statement:
--   Let $\mathbf X$ be a finite-dimensional Hilbert space and $f:\mathbf X\to\overline{\mathbb R}$ finite at $\bar x$, locally Lipschitz continuous around $\bar x$ relative to its domain, and parabolically epi-differentiable at $\bar x$ for $w\in T_{\operatorname{dom}f}(\bar x)$. Then
--
--   1. $\operatorname{dom}\mathrm df(\bar x)=T_{\operatorname{dom}f}(\bar x)$ and $\operatorname{dom}\mathrm d^2f(\bar x)(w\,|\,\cdot)=T^2_{\operatorname{dom}f}(\bar x,w)$;
--   2. $\operatorname{dom}f$ is parabolically derivable at $\bar x$ for $w$.
--
--   The result is cited from [24, Propositions 2.1 and 4.1].
--
--   **Formalization Note** "$f$ finite at $\bar x$" is part of the Lean predicate of local Lipschitz continuity around $\bar x$ and is not repeated.
--
--   Differences from the source:
--   - encoding: X a finite-dimensional Hilbert space (standing assumption, p.3) → E a real inner-product space with [FiniteDimensional ℝ E]; reason: the standing assumption of §2 written as a typeclass; same instances
--   - encoding: extended-real values in [−∞, ∞], quotients over f(x̄) finite → EReal, with the finite base subtracted as the real (f x̄).toReal; reason: Lean convention; on every instance where the paper's quotient is defined the two agree
--   - encoding: f finite at x̄, a separate assumption → no separate binder; finiteness of f(x̄) is a conjunct of LocLipRel; reason: local Lipschitz continuity around x̄ already supplies it; same instances
--   - encoding: |f(x) − f(y)| ≤ ℓ‖x − y‖ on U ∩ C for an extended-real f → LocLipRel: f finite on U ∩ C, with the inequality on the real values (f x).toReal; reason: the printed inequality with y = x̄ already forces finiteness on U ∩ C; same functions
--   - encoding: the standing “f(x̄) finite, df(x̄)(w) finite” before the definition of parabolic epi-differentiability, p.17 → conjuncts of ParabEpiDiffAt; reason: the page assumes both before defining the notion; they exclude only undefined cases
--   - encoding: an arc ξ : [0, ε] → C → ξ : ℝ → E with ξ(t) ∈ C on [0, ε], no continuity required; reason: the page states no continuity, and the proof of Proposition 2.4 builds ξ from a bare o(t²) term; values outside [0, ε] are never read
-- source:
--   A. Mohammadi, E. Sarabi, Parabolic Regularity of Spectral Functions, arXiv:2301.04240v3 (preprint basis), https://arxiv.org/abs/2301.04240v3, Proposition 4.6, p.17

import Mathlib
import Definitions.Def_SpectralParab_Basic
import Definitions.Def_SpectralParab_ParabolicReg
import Definitions.Def_SpectralParab_SymMatSpace
import Definitions.Def_SpectralParab_EigBlocks

open Filter Topology Matrix Asymptotics
open scoped RealInnerProductSpace
open SunNLSDP.Equiv ModernConvex.Spectral

namespace SpectralParab

/-- arXiv:2301.04240v3, Proposition 4.6, p.17 (cited from [24, Propositions 2.1 and 4.1]). Let
`f : X → R̄` on a finite-dimensional Hilbert space be finite at `x̄`, locally Lipschitz continuous
around `x̄` relative to its domain, and parabolically epi-differentiable at `x̄` for
`w ∈ T_{dom f}(x̄)`. Then
(a) `dom df(x̄) = T_{dom f}(x̄)` and `dom d²f(x̄)(w | ·) = T²_{dom f}(x̄, w)`;
(b) `dom f` is parabolically derivable at `x̄` for `w`.
**Formalization Note.** `FiniteDimensional ℝ E` is the paper's standing assumption (p.3).
Finiteness of `f(x̄)` is a conjunct of `LocLipRel`. `dom φ = {φ < ∞}`. -/
theorem proposition_4_6 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal) (xbar : E) (hlip : LocLipRel f (dom f) xbar)
    (w : E) (hw : w ∈ tangentCone (dom f) xbar) (hpe : ParabEpiDiffAt f xbar w) :
    ({w' | subderiv f xbar w' < ⊤} = tangentCone (dom f) xbar ∧
      {z | parabSubderiv f xbar w z < ⊤} = secondTangentSet (dom f) xbar w) ∧
    ParabDerivable (dom f) xbar w := by sorry

end SpectralParab
