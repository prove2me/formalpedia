-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_3_18
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_3_18
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:18:21.732151+00:00
-- url     : https://prove2.me/theorems/dfa4e679-01b0-4d06-90af-037a4dea1643
-- title:
--   Theorem 3.18
-- statement:
--   Suppose $-A$ generates either a bounded C0-semigroup on a Hilbert space or a bounded holomorphic C0-semigroup on a Banach space. Let $f,f'\in\mathcal B$. For $x\in D(A)$,
--
--   $$\lim_{t\downarrow0}\frac{f(tA)x-f(0)x}{t}=f'(0)Ax.$$
--
--   Conversely, when $f'(0)\ne0$, existence of this limit for $x\in X$ implies $x\in D(A)$ and the displayed identity. In particular $f'(0)=-1$ identifies the natural right derivative with $-A$. This extends the generator derivative beyond the exponential symbol.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 16, Theorem 3.18

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 3.18, arXiv:2202.03143v1, PDF page(s) 16. -/
theorem theorem_3_18
{X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
(A : DenseClosedGraphOperator X) (hA : HilbertGenerator A ∨ SectorialBelow A)
(f : AnalyticSymbol) (hf : BesovClass f) (hdf : BesovClass (deriv f)) :
    (∀ x y : X, (x, y) ∈ A.graph →
      Tendsto (fun t : ℝ => (t : ℂ)⁻¹ •
        (bOperator A (fun z => f ((t : ℂ) * z)) x - zeroValue f • x))
        (𝓝[>] 0) (𝓝 (zeroValue (deriv f) • y))) ∧
    (zeroValue (deriv f) ≠ 0 → ∀ x : X,
      (∃ v : X, Tendsto (fun t : ℝ => (t : ℂ)⁻¹ •
        (bOperator A (fun z => f ((t : ℂ) * z)) x - zeroValue f • x))
        (𝓝[>] 0) (𝓝 v)) →
      ∃ y : X, (x, y) ∈ A.graph ∧
        Tendsto (fun t : ℝ => (t : ℂ)⁻¹ •
          (bOperator A (fun z => f ((t : ℂ) * z)) x - zeroValue f • x))
          (𝓝[>] 0) (𝓝 (zeroValue (deriv f) • y))) ∧
    (zeroValue (deriv f) = -1 → ∀ x y : X,
      ((x, y) ∈ A.graph ↔
        Tendsto (fun t : ℝ => (t : ℂ)⁻¹ •
          (bOperator A (fun z => f ((t : ℂ) * z)) x - zeroValue f • x))
          (𝓝[>] 0) (𝓝 (-y)))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
