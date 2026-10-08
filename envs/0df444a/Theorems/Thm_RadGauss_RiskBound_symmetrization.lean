-- Prove2me | Theorems.Thm_RadGauss_RiskBound_symmetrization
-- name    : RadGauss.RiskBound.symmetrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:22:31.008414+00:00
-- url     : https://prove2.me/theorems/0c432d56-8d22-4b7e-a554-f7145175feeb
-- title:
--   Proof of Theorem 8 — symmetrization $\mathbf E\sup_{h\in\tilde\phi\circ F}(\mathbf Eh-\hat{\mathbf E}_nh)\le R_n(\tilde\phi\circ F)$
-- statement:
--   Let $P$ be a probability measure on $\mathcal X \times \mathcal Y$, let $\phi : \mathcal Y \times \mathcal A \to [0, 1]$ be measurable, let $F$ be a class of measurable maps $\mathcal X \to \mathcal A$, and let $n \ge 1$. For an i.i.d. sample $(X_i, Y_i)_{i=1}^n$ from $P$,
--
--   $$\mathbf E \sup_{h\in\tilde\phi\circ F}\bigl(\mathbf E h - \hat{\mathbf E}_n h\bigr) \le R_n(\tilde\phi\circ F),$$
--
--   where $R_n$ is the Rademacher complexity of Definition 2 (factor $2/n$, absolute value inside the supremum) with respect to $P$.
--
--   This is the step that turns the expected uniform deviation into the data-dependent complexity penalty of Theorem 8.
--
--   **Formalization Note** Three random variables are assumed measurable, exactly those the argument integrates: the uniform deviation $S \mapsto \sup_h(\mathbf Eh - \hat{\mathbf E}_nh)$, the empirical Rademacher complexity $S \mapsto \hat R_n(\tilde\phi\circ F)(S)$, and the double-sample deviation $(S, S') \mapsto \sup_h\bigl(\frac1n\sum_i h(S'_i) - \hat{\mathbf E}_n h\bigr)$; the paper does not discuss measurability. The hypothesis $n \ge 1$ is needed: at $n = 0$ Lean's $1/0 = 0$ makes the left side $\sup_h \mathbf Eh$, possibly positive, while $R_0 = 0$. The left side is a real expectation and enters via `ENNReal.ofReal`; the right side is in $[0,\infty]$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 468 (PDF p. 6), proof of Theorem 8, second display

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 468, last display), symmetrization:
`E sup_{h ∈ φ̃∘F} (E h − Ê_n h) ≤ R_n(φ̃∘F)` for an i.i.d. sample of size `n ≥ 1` from `P`.
The three random variables the argument integrates are assumed measurable: the uniform
deviation, the empirical Rademacher complexity of `φ̃∘F`, and the double-sample supremum
`(S, S') ↦ sup_{h ∈ φ̃∘F} ((1/n) Σ_i h(S'_i) − Ê_n h)`. -/
theorem symmetrization {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    ENNReal.ofReal
        (∫ S, supDev P n (phiTildeComp φ F) S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity P n (phiTildeComp φ F) := by sorry

end RadGauss.RiskBound
