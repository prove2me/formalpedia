-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_pure_symmetric_deFinetti
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.pure_symmetric_deFinetti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:58:48.344533+00:00
-- url     : https://prove2.me/theorems/e0b21ea6-9b63-4dd8-9b3e-1d862e005a6b
-- title:
--   Theorem 2: cited pure symmetric exponential de Finetti approximation
-- statement:
--   Let $n\ge0$, $k\ge1$, and $0\le r\le n$. For every unit vector $\psi$ in the symmetric subspace of $\mathcal H^{\otimes(n+k)}$, where $1\le d=\dim\mathcal H<\infty$, there exist a Borel probability measure $\nu$ on unit vectors $\theta\in\mathcal H$ and a measurable, integrable family $F_\theta$ of pure normalized almost-power projectors along $\theta$ such that $$\left\|\operatorname{Tr}_k|\psi\rangle\langle\psi|-\int F_\theta\,d\nu(\theta)\right\|_1\le2\exp\!\left[-\frac{k(r+1)}{2(n+k)}+\frac d2\ln k\right].$$ The trace norm is full. Purity and almost-power membership are conclusions for every direction. The source attributes the theorem to Renner; the single-site dimension in this pure version is not squared.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 14, Appendix Theorem 2: cited pure symmetric exponential de Finetti theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.14, Theorem 2, cited Theorem 4.3.2 of Renner (17).
The direction parameter is a unit vector. Every component is a PURE normalized
almost-power projector. Unlike the mixed-state bound (7), the exponent (12)
uses dim H, with no square. The probability measure and integrable Borel
family are conclusions, never hypotheses or an assumed approximation. -/
theorem pure_symmetric_deFinetti {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (n k r : ℕ) (hk : 0 < k) (hr : r ≤ n)
    (psi : Vec (Copies I (n + k))) (hpsi : IsState psi)
    (hsym : ∀ (pi : Equiv.Perm (Fin (n + k))) (x : Copies I (n + k)),
      psi (x ∘ pi) = psi x) :
    ∃ (nu : Measure {theta : Vec I // IsState theta})
      (family : {theta : Vec I // IsState theta} → Op (Copies I n)),
      IsProbabilityMeasure nu ∧ Measurable family ∧ Integrable family nu ∧
      (∀ theta, ∃ phi : Vec (Copies I n),
        AlmostPure theta.val n r phi ∧ family theta = pureDensity phi) ∧
      traceNorm (reduceCopies (pureDensity psi) n (by omega) - ∫ theta, family theta ∂nu) ≤
        2 * Real.exp (-((k : ℝ) * ((r : ℝ) + 1)) / (2 * ((n : ℝ) + k)) +
          (Fintype.card I : ℝ) / 2 * Real.log k) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
