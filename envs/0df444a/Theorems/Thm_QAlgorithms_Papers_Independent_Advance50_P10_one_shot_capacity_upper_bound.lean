-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_one_shot_capacity_upper_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.one_shot_capacity_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:49:27.30781+00:00
-- url     : https://prove2.me/theorems/dba6eb3e-815a-42cd-b8e4-fdd0f31cf2b1
-- title:
--   Theorem V.1: one-shot average-error capacity upper bound
-- statement:
--   All logarithms are base two. On a finite-dimensional complex Hilbert space $H$, write $S_\alpha(A\|B)$ for the paper’s unnormalized Petz Rényi relative entropy of positive semidefinite operators, with extended-real values, support-only powers, and the Umegaki value at order one. Let $X$ be an arbitrary nonempty alphabet and $W:X\to\mathcal S(H)$ a classical–quantum channel with density outputs. Input laws are nonnegative finitely supported probability laws. For such a law $p$, let $\widehat W_p=\sum_xp(x)|x\rangle\langle x|\otimes W_x$ and $\widehat p=\sum_xp(x)|x\rangle\langle x|$. Define $\chi_\alpha(p)=\inf_{\sigma\in\mathcal S(H)}S_\alpha(\widehat W_p\|\widehat p\otimes\sigma)$ and $\chi^*_{\alpha,1}(W)=\sup_p\chi_\alpha(p)$. A one-use code has a positive number $M$ of equiprobable messages, an arbitrary encoding into $X$, and a positive decoding POVM summing to the identity. Let $C_\varepsilon(W)$ be the supremum of $\log_2M$ for such codes with average error at most $\varepsilon$. For $0<\varepsilon<1$,
--
--   $$C_\varepsilon(W)\le\inf_{\alpha>1}\left\{\chi^*_{\alpha,1}(W)+\frac\alpha{\alpha-1}\log_2\frac1{1-\varepsilon}\right\}.$$
--
--   No compact-image hypothesis is needed. The error domain is the one used by the logarithm in the proof. This is the one-shot upper bound promised in the abstract.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 8, Theorem V.1: one-shot average-error capacity upper bound

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

/-- Theorem V.1, PDF p.8: the displayed logarithm's nontrivial probability domain
is 0<epsilon<1. Compactness of the image is not assumed in this section. -/
theorem one_shot_capacity_upper_bound {X I : Type} [Nonempty X] [Fintype I] [DecidableEq I]
    (W : X → Operator I) (hW : ∀ x, IsDensityMatrix (W x))
    (e : ℝ) (he : 0 < e) (he_one : e < 1) :
    cqOneShotCapacityBits e W ≤
      ⨅ a : {a : ℝ // 1 < a}, capacityOne a.1 W +
        ((a.1 / (a.1 - 1) * Real.logb 2 (1 / (1 - e)) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
