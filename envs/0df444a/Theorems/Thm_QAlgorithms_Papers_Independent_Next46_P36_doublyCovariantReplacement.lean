-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_doublyCovariantReplacement
-- name    : QAlgorithms.Papers.Independent.Next46.P36.doublyCovariantReplacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:39:45.865725+00:00
-- url     : https://prove2.me/theorems/58c9a42a-afad-48af-8cb7-b436e64ca35c
-- title:
--   Lemma 2: doubly covariant replacement preserves risk
-- statement:
--   Let $G$ be compact with normalized two-sided Haar measure and let $\Psi=\bigoplus_\mu c_\mu\operatorname{vec}(W_\mu)/\sqrt{d_\mu}$ be a normalized canonical input, with pairwise inequivalent unitary irreducible blocks and $\sum_\mu|c_\mu|^2=1$. Let the measurable real cost be left- and right-invariant. Every POVM $N$ with finite absolute joint cost has a normalized replacement $M(\hat g)=U_{\hat g}\Xi U_{\hat g}^\dagger$ satisfying
--
--   $$[\Xi,U_gV_g]=0,\qquad R_\Psi(M)=R_\Psi(N),\qquad V_g=\bigoplus_\mu I_{d_\mu}\otimes\overline{W_\mu^\dagger U_g^\mu W_\mu}.$$
--
--   When the incoming density is relative to Haar measure, the replacement is the double average $M(x)=\int dk\int dh\,U_k^\dagger V_h^\dagger N(kxh^{-1})V_hU_k$. The replacement assertion also allows incoming measurements with arbitrary finite reference measures.
--
--   Only invariance and integrability of the cost are used; Fourier sign conditions are unnecessary.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 5, Lemma 2 and Eq. (31)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.5 Lemma 2 and Eq.(31): replacement preserves the risk exactly.
The double-density formula is asserted when the incoming reference is Haar;
arbitrary reference measures are still included in the replacement claim. -/
theorem doublyCovariantReplacement
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg]
    (c : S → ℂ) (hn : (∑ s, Complex.normSq (c s)) = 1)
    (W : ∀ s, Matrix.unitaryGroup (Fin (D s).dim) ℂ)
    (cost : G → G → ℝ) (hi : InvariantCost cost)
    (hm : Measurable (Function.uncurry cost))
    (N : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G)
    (hN : CanonicalAdmissible D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) N) :
    ∃ Xi : Matrix (CanonicalIndex D) (CanonicalIndex D) ℂ,
    ∃ M : QAlgorithms.Measurements.DensityPOVM (CanonicalIndex D) G,
      NormalizedSeed D dg Xi ∧ M.reference = dg ∧
      (∀ g, M.density g = QAlgorithms.conjSuperop (canonicalAction D g) Xi) ∧
      (∀ g, Xi * (canonicalAction D g * rightAction D W g) =
        (canonicalAction D g * rightAction D W g) * Xi) ∧
      CanonicalAdmissible D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) M ∧
      risk D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) M =
        risk D dg cost (QAlgorithms.pureDensity (canonicalInput D c W)) N ∧
      (N.reference = dg → ∀ g, M.density g =
        ∫ k, ∫ h, (canonicalAction D k)ᴴ * (rightAction D W h)ᴴ *
          N.density (k * g * h⁻¹) * rightAction D W h * canonicalAction D k ∂dg ∂dg) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
