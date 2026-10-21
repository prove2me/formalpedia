-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_measurable_common_approximate_identity
-- name    : QAlgorithms.Papers.Independent.Next46.P06.measurable_common_approximate_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:48:46.046529+00:00
-- url     : https://prove2.me/theorems/bed24453-be3a-49e8-bd39-934b4b14fcf1
-- title:
--   §14, unnumbered: common measurable approximate identities
-- statement:
--   Let $(Z,\Sigma)$ be an arbitrary measurable space, $H$ a complex Hilbert space, and $\Phi$ a measurable calculus satisfying MFC1–MFC5. For arbitrary finite-valued measurable $f,g:Z\to\mathbb C$, define, with $n\in\mathbb N$,
--
--   $$e_n(x)=\frac{n+1}{n+1+|f(x)|+|g(x)|}.$$
--
--   The functions $e_n,e_nf,e_ng$ are bounded. The sequence is a common strong approximate identity for $f,g$: its evaluations are bounded and converge strongly to $I$, and for $h=f,g$ one has $\Phi(e_n)\Phi(h)\subseteq\Phi(h)\Phi(e_n)=\Phi(he_n)\in\mathcal L(H)$. The shift reindexes the source's positive integers and prevents zero denominators.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 40, §14, unnumbered: common measurable approximate identities

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

section Measurable

variable {Z H : Type*} [MeasurableSpace Z] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Section 14, PDF p.40: the concrete positive-index sequence is a common
STRONG approximate identity for arbitrary measurable f and g. Boundedness of
both regularized symbols is part of the conclusion, not an assumption. -/
theorem measurable_common_approximate_identity [CompleteSpace H] (Phi : MeasurableSymbol Z → Graph H)
    (hPhi : QAlgorithms.Papers.Independent.Claimed50.P05.Calculus Phi)
    (f g : MeasurableSymbol Z) :
    let e := measurableApproxSequence f g
    (∀ n, QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol (e n) ∧
      QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol
        (QAlgorithms.Papers.Independent.Claimed50.P05.times (e n) f) ∧
      QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol
        (QAlgorithms.Papers.Independent.Claimed50.P05.times (e n) g)) ∧
    (∀ n, Bounded (Phi (e n))) ∧
    (∀ h : MeasurableSymbol Z, h = f ∨ h = g → ∀ n,
      Bounded (Phi (QAlgorithms.Papers.Independent.Claimed50.P05.times h (e n))) ∧
      graphMul (Phi (e n)) (Phi h) ⊆ graphMul (Phi h) (Phi (e n)) ∧
      graphMul (Phi h) (Phi (e n)) =
        Phi (QAlgorithms.Papers.Independent.Claimed50.P05.times h (e n))) ∧
    (∀ x : H, Tendsto (fun n => graphValue (Phi (e n)) x) atTop (𝓝 x)) := by sorry

end Measurable

end QAlgorithms.Papers.Independent.Next46.P06

end
