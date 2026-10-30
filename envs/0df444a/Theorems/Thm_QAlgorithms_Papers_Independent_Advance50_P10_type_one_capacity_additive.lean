-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_type_one_capacity_additive
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.type_one_capacity_additive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:58:07.746842+00:00
-- url     : https://prove2.me/theorems/cb8e9976-5b3e-4a33-812f-d40748bbdf0b
-- title:
--   Proposition B.2: product additivity of the type-1 capacity
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Assume $\operatorname{ran}W$ is compact and $\alpha>1$. For the product-output channel $W^{(n)}(x_1,\ldots,x_n)=\bigotimes_{k=1}^nW_{x_k}$,
--
--   $$\chi^*_{\alpha,1}(W^{(n)})=n\chi^*_{\alpha,1}(W)\qquad(n\in\mathbb N).$$
--
--   The zeroth product is the scalar channel and has zero capacity. Only type 1 is claimed above order two. This is the additivity used in the asymptotic converse.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 11, Proposition B.2: product additivity of the type-1 capacity

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

/-- Proposition B.2, PDF p.11: product additivity of type-1 capacity, including
n=0's scalar tensor unit. No type-2 equality above order two is inferred. -/
theorem type_one_capacity_additive {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) (hcompact : IsCompact (Set.range W))
    (a : ℝ) (ha : 1 < a) (n : ℕ) :
    capacityOne a (cqWordChannel W n) = (n : EReal) * capacityOne a W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
