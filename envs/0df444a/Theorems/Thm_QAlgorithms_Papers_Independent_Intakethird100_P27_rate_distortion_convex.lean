-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P27_rate_distortion_convex
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P27.rate_distortion_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:14:03.961132+00:00
-- url     : https://prove2.me/theorems/adb16fff-9511-45da-b81d-86870e413426
-- title:
--   Convexity of the operational rates and regularized purification formula
-- statement:
--   Fix a finite-dimensional memoryless source with a unit purification $\psi_{RA}$, where $R$ is isomorphic to $A$, a finite nonempty reconstruction register $B$, and a positive distortion observable $\Delta_{RB}$. Let $R_a(D)$ be the infimum of achievable qubit rates for assistance $a$, where $a$ is unassisted, unlimited entanglement, or unlimited forward classical communication without prior entanglement. Codes use actual CPTP maps and quantum cost $\log_2\dim W$; distortion is the average expectation of $\Delta$ on the single-letter output marginals. For $D_1,D_2\ge0$ and $0\le\lambda\le1$,
--
--   $$R_a(\lambda D_1+(1-\lambda)D_2)\le\lambda R_a(D_1)+(1-\lambda)R_a(D_2).$$
--
--   The same inequality holds for $L(D)=\lim_{k\to\infty}k^{-1}\min_{\mathcal N^{(k)}:\bar d\le D}E_p((\mathrm{id}\otimes\mathcal N^{(k)})(\psi^{\otimes k}))$. The limit exists and equals $R_q(D)$. Here $E_p$ is entanglement of purification, optimized over all finite purifications; the block channel need not be a product channel.
--
--   This records time sharing, including the classically assisted companion statement and Appendix (50). Rates below feasible distortion are infinity, with zero-weight terms defined as zero; no fixed-block convexity is asserted.
--
--   The minima retain attainment: for every normalized finite density matrix on the displayed bipartite registers, a normalized finite purification attains its entanglement of purification. For every positive block length and nonempty distortion-feasible channel set, a channel attains the constrained purification minimum. Empty feasible sets still have extended value infinity.
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, PDF p. 4, Remark 5; p.6 companion sentence; Appendix (50)

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

/-- PDF pp.4,6,17, Remark 5 and (50): all three operational rate-distortion
functions are convex, as is the convergent regularized expression (9).
The minima in (3) and (9) retain attainment: normalized finite purifications
attain E_p on density matrices, and every nonempty positive-block feasible
channel set has an optimizer. No fixed-block convexity is asserted. -/
theorem rate_distortion_convex {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (S : DistortionSource A B)
    (a : LossyAssistance) (D1 D2 lam : ℝ) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (rateDistortion S a (lam * D1 + (1 - lam) * D2) ≤
      ENNReal.ofReal lam * rateDistortion S a D1 +
        ENNReal.ofReal (1 - lam) * rateDistortion S a D2) ∧
    (regularizedPurification S (lam * D1 + (1 - lam) * D2) ≤
      ENNReal.ofReal lam * regularizedPurification S D1 +
        ENNReal.ofReal (1 - lam) * regularizedPurification S D2) ∧
    (∀ D : ℝ, 0 ≤ D →
      Tendsto (fun k => purificationBlockValue S D (k + 1)) atTop
        (nhds (regularizedPurification S D)) ∧
      regularizedPurification S D = rateDistortion S .unassisted D ∧
      (∀ k : ℕ, 1 ≤ k →
        (∃ N : Superop (IidRegister A k) (IidRegister B k), IsChannel N ∧
          averageDistortion S (iidChannelOutput S k N) ≤ D) →
        ∃ N : Superop (IidRegister A k) (IidRegister B k), IsChannel N ∧
          averageDistortion S (iidChannelOutput S k N) ≤ D ∧
          ∀ M : Superop (IidRegister A k) (IidRegister B k), IsChannel M →
            averageDistortion S (iidChannelOutput S k M) ≤ D →
              purificationCost (iidChannelOutput S k N) ≤
                purificationCost (iidChannelOutput S k M))) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, IsDensityMatrix rho →
      purificationCost rho ∈ purificationValues rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P27

end
