-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_helstrom_equal_prior
-- name    : QAlgorithms.Papers.Independent.Bridge50.P44.helstrom_equal_prior
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:12:09.706045+00:00
-- url     : https://prove2.me/theorems/591e1bc2-f6ff-481b-a93b-dd05edfc7f40
-- title:
--   Theorem A.5: Helstrom equal-prior formula
-- statement:
--   Let $\rho,\sigma$ be density matrices on any finite-dimensional Hilbert space. A single copy of one state is supplied with equal prior probabilities. Optimize the guessing success probability over all binary POVMs. Then
--
--   $$p_{\mathrm{distinguish}}(\rho,\sigma)=\tfrac12+\tfrac12D(\rho,\sigma).$$
--
--   Here $D=\frac12\|\rho-\sigma\|_1$. This is the equal-prior Helstrom formula, cited to Helstrom [Hel76] and proved in Appendix A.2.
--
--   The maximum is attained: there exists a binary POVM whose equal-prior success equals the displayed optimum.
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, PDF p. 39, Theorem A.5: Helstrom equal-prior formula

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

/-- PDF pp.39--40, Theorem A.5 (Helstrom): one copy, equal priors.
The accepted mixed-state optimization is over actual binary POVMs, and an
attaining POVM is asserted explicitly, retaining the maximum on p.39. -/
theorem helstrom_equal_prior {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    mixedOptSuccess (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then sigma else rho) =
      1 / 2 + (1 / 2 : ℝ) * traceDistance rho sigma ∧
    ∃ M : Bool → Matrix I I ℂ, IsPOVM M ∧
      (1 / 2 : ℝ) * effectProb (M false) rho +
        (1 / 2 : ℝ) * effectProb (M true) sigma =
          mixedOptSuccess (fun _ : Bool => (1 / 2 : ℝ))
            (fun b => if b then sigma else rho) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P44

end
