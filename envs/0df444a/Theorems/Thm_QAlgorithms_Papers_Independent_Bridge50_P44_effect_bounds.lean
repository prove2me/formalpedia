-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_effect_bounds
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.effect_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:09:28.728848+00:00
-- url     : https://prove2.me/theorems/4f545fa4-d82d-454a-8cb0-25cd1f5e8a5d
-- title:
--   Lemma A.3: effect bounds and tightness
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices on an arbitrary finite-dimensional Hilbert space. For every effect $0\le M\le I$,
--
--   $$\operatorname{tr}[M(\rho-\sigma)]\le D(\rho,\sigma),\qquad |\operatorname{tr}[M(\rho-\sigma)]|\le\operatorname{tr}[M|\rho-\sigma|].$$
--
--   Each inequality is attained by some effect (the witnesses may differ). Consequently the first right-hand side is the maximum over effects. Here $D$ is half the trace norm, the absolute value of a Hermitian operator is its spectral absolute value, and the displayed traces are real.
--
--   The result provides both the variational characterization and the effect estimate used for measurements.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 37, Lemma A.3: effect bounds and tightness

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.37, Lemma A.3: both effect inequalities, and attainment of each.
The first upper bound and its witness express the maximum in Eq.(21). -/
theorem effect_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ M, IsEffect M →
      effectProb M (rho - sigma) ≤ traceDistance rho sigma ∧
      |effectProb M (rho - sigma)| ≤ effectProb M (cfc (fun x : ℝ => |x|) (rho - sigma))) ∧
    (∃ M, IsEffect M ∧ effectProb M (rho - sigma) = traceDistance rho sigma) ∧
    (∃ M, IsEffect M ∧
      |effectProb M (rho - sigma)| = effectProb M (cfc (fun x : ℝ => |x|) (rho - sigma))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
