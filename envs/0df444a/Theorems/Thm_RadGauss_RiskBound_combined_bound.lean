-- Prove2me | Theorems.Thm_RadGauss_RiskBound_combined_bound
-- name    : RadGauss.RiskBound.combined_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:22:18.193878+00:00
-- url     : https://prove2.me/theorems/c9959444-d35e-456b-b0c7-8c4e39d990f1
-- title:
--   Proof of Theorem 8 — w.p. $\ge 1-\delta$, $\mathbf E\mathcal L\le\hat{\mathbf E}_n\phi+\mathbf E\sup(\mathbf Eh-\hat{\mathbf E}_nh)+\sqrt{8\ln(2/\delta)/n}$ for all $f\in F$
-- statement:
--   Let $\mathcal L : \mathcal Y \times \mathcal A \to [0, 1]$ be a measurable loss and $\phi : \mathcal Y \times \mathcal A \to [0, 1]$ a measurable cost that dominates it, $\phi(y, a) \ge \mathcal L(y, a)$ for all $y, a$. Let $F$ be a class of measurable maps $\mathcal X \to \mathcal A$, $P$ a probability measure on $\mathcal X \times \mathcal Y$, $n \ge 1$ and $0 < \delta < 1$, and let $(X_i, Y_i)_{i=1}^n$ be an i.i.d. sample from $P$, with $(X, Y)$ a fresh draw from $P$. Then with probability at least $1 - \delta$, every $f \in F$ satisfies
--
--   $$\mathbf E\mathcal L(Y, f(X)) \le \hat{\mathbf E}_n\phi(Y, f(X)) + \mathbf E \sup_{h\in\tilde\phi\circ F}\bigl(\mathbf E h - \hat{\mathbf E}_n h\bigr) + \sqrt{\frac{8\ln(2/\delta)}{n}} .$$
--
--   The event is uniform over $F$: a single sample works for every $f$ simultaneously. This is Theorem 8 with the expected uniform deviation in place of the Rademacher complexity; the remaining step is symmetrization.
--
--   **Formalization Note** The uniform deviation is assumed measurable as a function of the sample (the mission's measurability guard). The statement bounds the (outer) measure of the set of samples on which some $f \in F$ violates the inequality by $\delta$. The constant $\sqrt{8}$ is the printed one.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 468 (PDF p. 6), proof of Theorem 8, first display

import Mathlib
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp

open MeasureTheory

namespace RadGauss.RiskBound

/-- **Proof of Theorem 8** (p. 468, first display): with probability at least `1 − δ` over an i.i.d.
sample of size `n ≥ 1` from `P`, every `f ∈ F` satisfies
`E L(Y, f(X)) ≤ Ê_n φ(Y, f(X)) + E sup_{h ∈ φ̃∘F} (E h − Ê_n h) + √(8 ln(2/δ)/n)`.
The uniform deviation is assumed measurable as a function of the sample. -/
theorem combined_bound {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F))) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ ((∫ z, L z.2 (f z.1) ∂P) ≤
          empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (8 * Real.log (2 / δ) / n))}
      ≤ ENNReal.ofReal δ := by sorry

end RadGauss.RiskBound
