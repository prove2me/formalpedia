-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P27_classical_assistance_formation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P27.classical_assistance_formation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:15:50.110112+00:00
-- url     : https://prove2.me/theorems/ac73b95b-c79c-4429-87ee-7668ceb54125
-- title:
--   Forward classical assistance is characterized by regularized formation
-- statement:
--   Fix a finite-dimensional memoryless source $\rho_A$, a unit purification $\psi_{RA}$ with $R\simeq A$, a finite nonempty reconstruction register $B$, and a positive observable $\Delta_{RB}$. For $D\ge0$, let $R^q_{\to}(D)$ be the infimum of asymptotically achievable quantum communication rates using unlimited noiseless forward classical communication and no prior entanglement. The encoder is a quantum instrument with quantum message $W$ and classical message $M$; Bob applies an $M$-conditioned CPTP decoder. The quantum cost per block is $\log_2\dim W$.
--
--   For any block channel $\mathcal N^{(k)}:A^k\to B^k$, put $\omega^{(k)}=(\mathrm{id}_{R^k}\otimes\mathcal N^{(k)})(\psi^{\otimes k})$, and let $\bar d$ be its average single-letter observable distortion. Then
--
--   $$R^q_{\to}(D)=\lim_{k\to\infty}\frac1k\min_{\mathcal N^{(k)}:\bar d\le D}E_F(\omega^{(k)}).$$
--
--   The limit exists, and each nonempty feasible positive-block channel set has an attaining minimizer. $E_F$ is entanglement of formation across $R^k:B^k$, in bits. If distortion is infeasible, the infimum convention gives infinity on both sides.
--
--   This realizes the abstract's formation characterization in the general observable-distortion model.
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, PDF p. 6, Theorem 10; abstract seed p.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P27

open Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRB mutualInformation bipartiteBlock epr)

open QAlgorithms.Papers.Independent.Information100.P08 (formation)

open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

open QAlgorithms.Papers.Independent.Bridge50.P37 (isotropicState normalizedEntangledProjection)

/-- PDF pp.6--8, Theorem 10, realizing the abstract seed on p.1: convergence to
the independently operational forward-classically-assisted rate, together with
attainment of every feasible positive-block outer minimum. No limit, entropy
identity, or optimizing channel is assumed. Below feasibility the values are infinity. -/
theorem classical_assistance_formation {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (S : DistortionSource A B) (D : ℝ) (hD : 0 ≤ D) :
    Tendsto (fun k => formationBlockValue S D (k + 1)) atTop
      (nhds (rateDistortion S .classical D)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (∃ N : Superop (IidRegister A k) (IidRegister B k), IsChannel N ∧
        averageDistortion S (iidChannelOutput S k N) ≤ D) →
      ∃ N : Superop (IidRegister A k) (IidRegister B k), IsChannel N ∧
        averageDistortion S (iidChannelOutput S k N) ≤ D ∧
        ∀ M : Superop (IidRegister A k) (IidRegister B k), IsChannel M →
          averageDistortion S (iidChannelOutput S k M) ≤ D →
            formation (iidChannelOutput S k N) ≤ formation (iidChannelOutput S k M)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P27

end
