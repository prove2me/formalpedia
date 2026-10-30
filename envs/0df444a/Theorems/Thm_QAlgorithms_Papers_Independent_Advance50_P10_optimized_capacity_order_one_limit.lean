-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_optimized_capacity_order_one_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.optimized_capacity_order_one_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:00:14.426576+00:00
-- url     : https://prove2.me/theorems/a0978413-7ff0-4f23-9200-cae7ff8d24d3
-- title:
--   Proposition B.5: order-one limit of optimized capacity
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. For every such channel, with no compact-image hypothesis,
--
--   $$\lim_{\alpha\to1}\chi^*_{\alpha,1}(W)=\chi^*_{1,1}(W).$$
--
--   The limit is two-sided. The right side is the ordinary Holevo capacity. The printed proof uses the compact quotient from B.4 without explicitly assuming a compact image; this proof-level gap is recorded without adding a premise to the stated proposition.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 12, Proposition B.5: order-one limit of optimized capacity

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

/-- Proposition B.5, PDF p.12: two-sided order-one limit of type-1 capacity.
No compact-image hypothesis is printed. Its proof invokes B.4 as though the image
were compact; that proof-level gap is documented without strengthening the hypotheses. -/
theorem optimized_capacity_order_one_limit {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) :
    Tendsto (fun a => capacityOne a W) (𝓝[≠] 1) (𝓝 (capacityOne 1 W)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
