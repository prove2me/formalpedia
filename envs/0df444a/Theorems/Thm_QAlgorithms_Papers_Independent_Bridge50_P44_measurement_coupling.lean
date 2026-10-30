-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_measurement_coupling
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.measurement_coupling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:14:27.272088+00:00
-- url     : https://prove2.me/theorems/602e4459-8f40-45d0-b754-80f2215184de
-- title:
--   Corollary A.7: coupling measurement outcomes
-- statement:
--   Let $\rho,\sigma$ be finite-dimensional density matrices with $D(\rho,\sigma)\le\varepsilon$, and apply the same discrete POVM $\{\Gamma_w\}$ to both. Its outcome laws are $P(w)=\operatorname{tr}(\Gamma_w\rho)$ and $Q(w)=\operatorname{tr}(\Gamma_w\sigma)$. There exists a coupling $J$ of these laws such that
--
--   $$\Pr_J[W\ne\widetilde W]\le D(\rho,\sigma).$$
--
--   The coupling is chosen after the POVM. The statement gives no common coupling for incompatible measurements and no decomposition of the quantum states as a physical mixture.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 42, Corollary A.7: coupling measurement outcomes

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

/-- PDF p.42, Corollary A.7: for each common POVM there exists a coupling
of its outcome laws; no simultaneous coupling of incompatible POVMs is asserted. -/
theorem measurement_coupling {I O : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : traceDistance rho sigma ≤ epsilon)
    (M : O → Matrix I I ℂ) (hM : IsDiscretePOVM M) :
    ∃ j : O × O → ℝ,
      IsCoupling (fun o => effectProb (M o) rho) (fun o => effectProb (M o) sigma) j ∧
      (∑' z : O × O, if z.1 ≠ z.2 then j z else 0) ≤ traceDistance rho sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
