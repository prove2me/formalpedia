-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_asymptotic_capacity_converse
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.asymptotic_capacity_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:50:50.098467+00:00
-- url     : https://prove2.me/theorems/f6d0dbc8-c39b-4468-83d3-1d637700fdc8
-- title:
--   Theorem V.2: asymptotic epsilon-capacity converse
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. Assume $\operatorname{ran}W$ is compact. The product channel is $W^{(n)}(x_1,\ldots,x_n)=W_{x_1}\otimes\cdots\otimes W_{x_n}$. For a sequence of actual codes $C^{(n)}$, define its rate as $R=\liminf_n n^{-1}\log_2M_n$. Let $\overline C_\varepsilon(W)$ be the supremum of these rates over sequences whose average errors have limsup at most $\varepsilon$. Then
--
--   $$\overline C_\varepsilon(W)\le\chi^*_{1,1}(W)\qquad(0\le\varepsilon<1).$$
--
--   This covers zero error and nonvanishing allowed errors for product encodings, without entangled-input or adaptive assistance.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 9, Theorem V.2: asymptotic epsilon-capacity converse

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

/-- Theorem V.2, PDF p.9: the asymptotic product-encoding converse, including
zero error and nonvanishing allowed errors below one. -/
theorem asymptotic_capacity_converse {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x)) (hcompact : IsCompact (Set.range W))
    (e : ℝ) (he : 0 ≤ e) (he_one : e < 1) :
    asymptoticCapacity e W ≤ capacityOne 1 W := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
