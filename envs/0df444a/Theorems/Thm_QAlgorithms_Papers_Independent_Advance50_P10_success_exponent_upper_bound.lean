-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_success_exponent_upper_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.success_exponent_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:51:32.268969+00:00
-- url     : https://prove2.me/theorems/7e78599a-88a3-4cea-8319-f0ee7f3c1314
-- title:
--   Remark V.3: operational success-exponent bound
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Assume $\operatorname{ran}W$ is compact. For any sequence $C^{(n)}$ of positive-message product-encoding codes, let $P_s(C^{(n)})$ be its average success probability and $R=\liminf_n n^{-1}\log_2M_n$ its rate. For every $\alpha>1$,
--
--   $$\limsup_{n\to\infty}\frac1n\log_2P_s(C^{(n)})\le\frac{\alpha-1}{\alpha}\bigl(\chi^*_{\alpha,1}(W)-R\bigr).$$
--
--   Extended values retain zero success and an infinite rate. Only the operational exponent inequality is asserted here; the printed positive-slope cutoff corollary has its own deferred node.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 9, Remark V.3: operational success-exponent bound

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

/-- Remark V.3, PDF p.9: the operational success-exponent inequality.
The ambiguous positive-slope cutoff corollary is separately deferred. -/
theorem success_exponent_upper_bound {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) (hcompact : IsCompact (Set.range W))
    (a : ℝ) (ha : 1 < a) (C : CodeSequence X I) :
    successExponent W C ≤ (((a - 1) / a : ℝ) : EReal) * (capacityOne a W - cqSequenceRateBits C) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
