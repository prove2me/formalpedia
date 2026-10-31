-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_3_4
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_3_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:13:59.159986+00:00
-- url     : https://prove2.me/theorems/8907cf53-a94f-456e-aac2-c646eb32fb0e
-- title:
--   Proposition 3.4
-- statement:
--   For $f\in\mathcal B$, its derivative belongs to $W$ and, for $z\in\mathbb C_+$,
--
--   $$f(z)=f(\infty)+Q(f')(z)=f(\infty)-\frac2\pi\int_0^\infty\!\alpha\int_{\mathbb R}\frac{f'(\alpha+i\beta)}{(\alpha-i\beta+z)^2}\,d\beta\,d\alpha.$$
--
--   The map $Q$ is bounded linear from $W$ into $\mathcal B_0$ and restricts to a bijection from its holomorphic subspace onto $\mathcal B_0$. This is the scalar reproducing formula underlying the operator calculus.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 8, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 3.4, arXiv:2202.03143v1, PDF page(s) 8. -/
theorem proposition_3_4
:
    (∀ f, BesovClass f → MixedDerivativeClass (deriv f) ∧ ∀ z ∈ hp,
      AbsoluteDouble (qKernel (deriv f) z) ∧
      f z = infinityValue f + besovPrimitive (deriv f) z) ∧
    (∀ g, MixedDerivativeClass g → BZero (besovPrimitive g)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ g, MixedDerivativeClass g → bSize (besovPrimitive g) ≤ ENNReal.ofReal C * wSize g) ∧
    (∀ c : ℂ, ∀ g h, MixedDerivativeClass g → MixedDerivativeClass h → EqOn (besovPrimitive (c • g + h)) (c • besovPrimitive g + besovPrimitive h) hp) ∧
    (∀ g h, MixedDerivativeClass g → MixedDerivativeClass h →
      (fun p : ℝ × ℝ => g (point p.1 p.2)) =ᵐ[positiveVolume.prod volume]
        (fun p : ℝ × ℝ => h (point p.1 p.2)) → EqOn (besovPrimitive g) (besovPrimitive h) hp) ∧
    (∀ f, BZero f → ∃ g, MixedDerivativeClass g ∧ Hol hp g ∧ EqOn (besovPrimitive g) f hp) ∧
    (∀ g h, MixedDerivativeClass g → Hol hp g → MixedDerivativeClass h → Hol hp h →
      EqOn (besovPrimitive g) (besovPrimitive h) hp → EqOn g h hp) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
