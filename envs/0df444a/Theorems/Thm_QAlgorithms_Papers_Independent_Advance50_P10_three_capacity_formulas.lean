-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_three_capacity_formulas
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.three_capacity_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:48:37.082459+00:00
-- url     : https://prove2.me/theorems/ec5febc8-21b5-4cec-a10e-4e45f941d162
-- title:
--   Theorem IV.8: three capacity formulas coincide
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Assume $\operatorname{ran}W$ is compact. Define the type-2 capacity by $\chi^*_{\alpha,2}(W)=\sup_p\inf_\sigma\sum_xp(x)S_\alpha(W_x\|\sigma)$, and the radius by $R_{S_\alpha}(\operatorname{ran}W)=\inf_\sigma\sup_xS_\alpha(W_x\|\sigma)$, with density centres. For $0<\alpha\le2$,
--
--   $$\chi^*_{\alpha,1}(W)=\chi^*_{\alpha,2}(W)=R_{S_\alpha}(\operatorname{ran}W).$$
--
--   Order one is included. The type-0 capacity is not part of this equality, which is the second main result promised in the abstract.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 7, Theorem IV.8: three capacity formulas coincide

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Theorem IV.8, PDF pp.7–8: equality of types 1 and 2 and the divergence
radius for a cq channel of compact image. Order one is included; type zero is absent. -/
theorem three_capacity_formulas {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) (hcompact : IsCompact (Set.range W))
    (a : ℝ) (ha : 0 < a) (ha_two : a ≤ 2) :
    capacityOne a W = capacityTwo a W ∧ capacityTwo a W = divergenceRadiusBits (petzRelativeBits a) W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
