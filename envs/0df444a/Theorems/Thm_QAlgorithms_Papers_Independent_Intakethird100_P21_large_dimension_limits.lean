-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_large_dimension_limits
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.large_dimension_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:04:38.013015+00:00
-- url     : https://prove2.me/theorems/b743af20-c8dd-4d4d-9040-220bc6d1d968
-- title:
--   Fixed-fidelity large-dimension limits
-- statement:
--   Fix any $F\in[0,1]$. For each dimension $d\ge2$, let $\rho_{d,F}=FP_d+(1-F)(I-P_d)/(d^2-1)$ be the isotropic density, with $P_d$ the maximally entangled projector. Its tangle $\tau$ is the convex roof of pure squared I-concurrence and its concurrence $C$ is the roof of pure I-concurrence. Then
--
--   $$
--   \lim_{d\to\infty}\tau(\rho_{d,F})=2F,\qquad
--   \lim_{d\to\infty}C(\rho_{d,F})=\sqrt2\,F.
--   $$
--
--   These are limits of scalar entanglement values in changing dimensions, with fidelity fixed before the limit. Both endpoint fidelities are included; no uniform convergence rate is asserted.
--
--   **Formalization Note** The sequence is indexed by dimensions $d=n+2$, removing the two nonphysical initial indices without altering the limit.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 13, §3.4.3: fixed-fidelity large-d limits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.13: fixed-F dimension limits, including F=0 and F=1.
Using dimension n+2 removes the two nonphysical initial indices without
asserting a convergence rate or uniform convergence in F. -/
theorem large_dimension_limits (F : ℝ) (hF : F ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => tangle (isotropicDensityAtFidelity (n+2) F)) atTop (nhds (2*F)) ∧
    Tendsto (fun n : ℕ => concurrence (isotropicDensityAtFidelity (n+2) F)) atTop (nhds (Real.sqrt 2 * F)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
