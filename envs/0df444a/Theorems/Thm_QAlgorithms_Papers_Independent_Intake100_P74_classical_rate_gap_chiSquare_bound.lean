-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_classical_rate_gap_chiSquare_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.classical_rate_gap_chiSquare_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:01:59.268294+00:00
-- url     : https://prove2.me/theorems/74c875fc-be1b-4887-a66e-f2c9929055d0
-- title:
--   Classical chi-square upper bound for the thermal rate gap
-- statement:
--   Fix $m\ge2$, $N>0$, $0\le k\le1$, and $N_c\ge0$. Let $X_m$ be a finite real law with nonnegative normalized weights, mean zero and second moment one, and use two independent copies in $Z_m=\sqrt{N/2}(X_m+iX'_m)$. Let $\rho_m$ be the average output of the attenuation-plus-noise channel and $N'=k^2N+N_c$. All entropies are in nats. Write $g(t)=(t+1)\log(t+1)-t\log t$, with $0\log0=0$. The output entropy is finite and at most $g(N')$. The Holevo-information gap is $\Delta_B=g(N')-H(\rho_m)$, since the common conditional entropy $g(N_c)$ cancels. If $N'>0$, use $s=k^2N/(\sqrt{N'(N'+1)}-k^2N)$, $Y_m=\sqrt{s}X_m+G$, and $Y\sim\mathcal N(0,1+s)$. Then
--
--   $$\Delta_B\le(1+\chi^2(P_{Y_m},P_Y))^2-1.$$
--
--   The right side may be infinite. If $N'=0$, the gap is zero, without evaluating the displayed quotient. The square uses the identical law in both coordinates; this is an upper bound on the quantum rate loss.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 5, §4 (12): classical chi-square bound on the quantum rate gap

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P74

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P74

open MeasureTheory

open scoped BigOperators ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient thermalMatrix)

open QAlgorithms.Papers.Independent.Support50.P14 (photonEnergy)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal spectralEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, (12): iid centered variance-one finite coordinates, with the
square appropriate to identical laws. The complete replacing-vacuum endpoint
has zero gap and is never fed to the comparison SNR formula. -/
theorem classical_rate_gap_chiSquare_bound
    (m : ℕ) (hm : 2 ≤ m) (k Nc N : ℝ)
    (hk : 0 ≤ k) (hkUpper : k ≤ 1) (hNc : 0 ≤ Nc) (hN : 0 < N)
    (p x : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hpTotal : ∑ j, p j = 1)
    (hxMean : ∑ j, p j * x j = 0) (hxVariance : ∑ j, p j * (x j) ^ 2 = 1) :
    singleModeEntropy (constellationOutput k Nc N (finiteRealLaw p x)
      (finiteRealLaw p x)) ≤ ENNReal.ofReal (g (k ^ 2 * N + Nc)) ∧
    (0 < k ^ 2 * N + Nc →
      classicalInformationGap k Nc N (finiteRealLaw p x) ≤
        (1 + classicalChiSquare (comparisonSnr k Nc N) (finiteRealLaw p x)) ^ 2 - 1) ∧
    (k ^ 2 * N + Nc = 0 → classicalInformationGap k Nc N (finiteRealLaw p x) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
