-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P56_generalized_trotter_limit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P56.generalized_trotter_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:55:38.106116+00:00
-- url     : https://prove2.me/theorems/f19915da-3e49-4045-822a-4a07166ab162
-- title:
--   Lemma 24
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces with nonempty finite bases. States are positive semidefinite operators of trace one; pure kets have norm one. All marginal states below are partial traces of the stated joint state. Logarithms are natural, and spectral powers vanish on the kernel, including at exponent zero.
--
--   Let $\rho,\sigma$ be positive definite density operators and $\mathcal N$ a strict CPTP map, meaning complete positivity and trace preservation together with positive-definiteness preservation after tensoring any finite identity reference. If $\mathcal N^\dagger$ is its Hilbert–Schmidt adjoint, then
--
--   $$\lim_{p\to0,\,p\ne0}\left[\sigma^{p/2}\mathcal N^\dagger\!\left(\mathcal N(\sigma)^{-p/2}\mathcal N(\rho)^p\mathcal N(\sigma)^{-p/2}\right)\sigma^{p/2}\right]^{1/p}=\exp\!\left(\log\sigma+\mathcal N^\dagger(\log\mathcal N(\rho)-\log\mathcal N(\sigma))\right).$$
--
--   The limit is two-sided in operator norm, and the final exponential is the ordinary matrix exponential. This supplies the generalized product limit used for relative-entropy differences.
-- source:
--   Rényi squashed entanglement, discord, and relative entropy differences, arXiv:1410.1443v3, PDF p. 24, Lemma 24

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

/-- arXiv:1410.1443v3, PDF p.24, Lemma 24, (6.6).
Punctured two-sided limit in the finite-dimensional operator-norm topology;
the final exponential is the ordinary matrix exponential of a Hermitian sum. -/
theorem generalized_trotter_limit (rho sigma : Op A) (N : Superop A B)
    (hrho : IsDensityMatrix rho) (hprho : rho.PosDef)
    (hsigma : IsDensityMatrix sigma) (hpsigma : sigma.PosDef) (hN : StrictChannel N) :
    Tendsto (fun p : ℝ =>
      let S := supportPower sigma (p/2)
      let T := supportPower (N sigma) (-p/2)
      supportPower (S * channelAdjoint N (T * supportPower (N rho) p * T) * S) (1/p))
      (nhdsWithin 0 {p : ℝ | p ≠ 0})
      (nhds (NormedSpace.exp (cfc Real.log sigma +
        channelAdjoint N (cfc Real.log (N rho) - cfc Real.log (N sigma))))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P56

end
