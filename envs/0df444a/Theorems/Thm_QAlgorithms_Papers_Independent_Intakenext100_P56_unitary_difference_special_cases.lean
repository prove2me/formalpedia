-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_unitary_difference_special_cases
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.unitary_difference_special_cases
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:02:49.219022+00:00
-- url     : https://prove2.me/theorems/357792d1-7dad-4c91-8953-23057c25491c
-- title:
--   Unnumbered: unitary-channel special cases of Conjecture 26
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\rho,\sigma$ be positive definite density operators, and $\mathcal U(Z)=UZU^\dagger$ a unitary channel. The following two separate comparisons hold:
--
--   $$0\le\alpha\le\beta,\ \alpha+\beta=2\quad\Longrightarrow\quad\Delta_\alpha(\rho,\sigma,\mathcal U)\le\Delta_\beta(\rho,\sigma,\mathcal U),$$
--   $$0<\alpha\le\beta,\ 1/\alpha+1/\beta=2\quad\Longrightarrow\quad\widetilde\Delta_\alpha(\rho,\sigma,\mathcal U)\le\widetilde\Delta_\beta(\rho,\sigma,\mathcal U).$$
--
--   The order-one branches use the ordinary relativeEntropyDifference and the first zero-order expression uses the support-power formula. The conclusion is confined to unitary channels and assumes no global conjecture.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 26, Unnumbered: unitary-channel special cases of Conjecture 26

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P56

noncomputable section

open Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P56

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw entropy average holevo)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz extendedLog marginalAB)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartiteProduct)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Advance50.P25 (renyiEntropyNats)

variable {A B C D E X : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype X]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E] [Nonempty X]

open scoped Matrix.Norms.L2Operator

/-- arXiv:1410.1443v3, PDF p.26: two separate unitary-channel special
cases. The erroneous rightmost exponent in (6.22) is read from (6.13). -/
theorem unitary_difference_special_cases (rho sigma : Op A)
    (hrho : IsDensityMatrix rho) (hprho : rho.PosDef)
    (hsigma : IsDensityMatrix sigma) (hpsigma : sigma.PosDef)
    (U : Matrix.unitaryGroup A ℂ) :
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → a+b=2 →
      differencePetz a rho sigma (conjSuperop (U : Op A)) ≤
        differencePetz b rho sigma (conjSuperop (U : Op A))) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b → 1/a+1/b=2 →
      differenceSandwiched a rho sigma (conjSuperop (U : Op A)) ≤
        differenceSandwiched b rho sigma (conjSuperop (U : Op A))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
