-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_density_minimizer_exists
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.density_minimizer_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:50:11.268648+00:00
-- url     : https://prove2.me/theorems/61605f9c-2e72-4b5a-8c12-6b5b9e2846cb
-- title:
--   §6, (6.8)–(6.9): mixed-norm density minimizers exist
-- statement:
--   Let $X$ be a density on a nonzero finite bipartite register and let $p>1$ be finite and real. Write $X_1=\operatorname{Tr}_2X$ and define $v(p,B)=X^{1/2}(B^{1/p-1}\otimes I)X^{1/2}$ for density matrices $B$ satisfying $\ker B\subseteq\ker X_1$. Assign objective $+\infty$ to incompatible $B$. There exists such a density $B$ with
--
--   $$\|v(p,B)\|_p=\|X\|_{(1,p)}=\inf_{C\in\mathcal D}\|v(p,C)\|_p.$$
--
--   Compatible singular $B$ are allowed, with powers on the support. This is the attainment conclusion (6.8)–(6.9); it does not assume the printed, invalid global continuity claim at incompatible singular densities.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 29, §6, (6.8)–(6.9): mixed-norm density minimizers exist

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

/-- (6.8)–(6.9), PDF p.29: a support-compatible density minimizer exists for
all finite real p>1. No false continuity assertion at incompatible singular B is assumed. -/
theorem density_minimizer_exists {D I : Type} [Fintype D] [Fintype I]
    [Nonempty D] [Nonempty I] (X : Mat (D × I)) (hX : IsDensityMatrix X)
    (p : ℝ) (hp : 1 < p) :
    ∃ B : Mat D, AdmissibleDensity X B ∧
      minimizerObjective p X B = mixedSize 1 (ENNReal.ofReal p) X ∧
      minimizerObjective p X B = ⨅ C : Mat D, minimizerObjective p X C := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
