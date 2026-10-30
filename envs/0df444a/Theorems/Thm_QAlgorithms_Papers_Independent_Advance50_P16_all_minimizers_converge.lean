-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_all_minimizers_converge
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.all_minimizers_converge
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:42:02.344796+00:00
-- url     : https://prove2.me/theorems/7d1777d9-0084-4b6d-b10b-923ac210c5a7
-- title:
--   Corollary 18: convergence of all mixed-norm minimizers
-- statement:
--   Let $X$ be a density matrix on $\mathbb C^d\otimes\mathbb C^n$, $d,n\ge1$, and put $X_1=\operatorname{Tr}_2X$. For every $p\in(1,2]$, choose any density $B(p)$ with $\ker B(p)\subseteq\ker X_1$ that minimizes the variational mixed-norm objective, so that
--
--   $$\left\|X^{1/2}(B(p)^{1/p-1}\otimes I_n)X^{1/2}\right\|_p=\|X\|_{(1,p)}.$$
--
--   Powers are computed on the support and incompatible supports have objective $+\infty$. Every such selection, without a continuity or full-rank assumption, satisfies
--
--   $$\lim_{p\downarrow1}B(p)=X_1.$$
--
--   Convergence is in the usual finite-dimensional matrix topology. This identifies the common limit of all minimizing choices.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 32, Corollary 18: convergence of all mixed-norm minimizers

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Corollary 18, PDF p.32 (proof pp.29–32): every selection of support-compatible
minimizers on (1,2] converges. No continuity or full rank of the selection is assumed. -/
theorem all_minimizers_converge {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (X : Mat (D × I)) (hX : IsDensityMatrix X)
    (B : ℝ → Mat D)
    (hB : ∀ p ∈ Ioc (1 : ℝ) 2, AdmissibleDensity X (B p) ∧
      minimizerObjective p X (B p) = mixedSize 1 (ENNReal.ofReal p) X) :
    Tendsto B (𝓝[>] 1) (𝓝 (traceRight X)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
