-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_randomWalk_gap_inverse_cardinality
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.randomWalk_gap_inverse_cardinality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:04:05.777045+00:00
-- url     : https://prove2.me/theorems/b4f26df6-7cad-4ca1-804d-8d901483b859
-- title:
--   Inverse-cardinality random-walk thermal-channel gap
-- statement:
--   Fix $0\le k\le1$, $N_c\ge0$ and finite $N>0$. For $m\ge2$, let $X_m$ be a symmetric walk of $m-1$ unit steps divided by $\sqrt{m-1}$. Its point $(2j-(m-1))/\sqrt{m-1}$ has probability $\binom{m-1}{j}/2^{m-1}$ for $0\le j\le m-1$. Use independent copies in $Z_m=\sqrt{N/2}(X_m+iX'_m)$ and let $\rho_m$ be the actual average channel output. Put $N'=k^2N+N_c$ and $\Delta_B(m)=g(N')-H(\rho_m)$ in nats. Then
--
--   $$\exists C>0\;\exists m_0\ge2\;\forall m\ge m_0:\quad \Delta_B(m)\le\frac{C}{m^2}.$$
--
--   The constants depend only on the fixed channel and energy. At $k=0$ every gap is zero. This is an upper bound inverse in the number $m^2$ of complex signals, and does not claim a matching lower bound.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 6, §4: inverse-cardinality random-walk gap

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

/-- PDF pp.3,5--6: inverse complex-constellation-cardinality random-walk
gap O(m^(-2)); m real points give m² complex signals. Constants may depend
on fixed k,Nc,N but not m. This is an upper bound, not a matching lower bound. -/
theorem randomWalk_gap_inverse_cardinality
    (k Nc N : ℝ) (hk : 0 ≤ k) (hkUpper : k ≤ 1) (hNc : 0 ≤ Nc) (hN : 0 < N) :
    (∃ C : ℝ, 0 < C ∧ ∃ m0 : ℕ, 2 ≤ m0 ∧ ∀ m ≥ m0,
      classicalInformationGap k Nc N (randomWalkLaw m) ≤
        ENNReal.ofReal (C / (m : ℝ) ^ 2)) ∧
    (k = 0 → ∀ m ≥ 2, classicalInformationGap k Nc N (randomWalkLaw m) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
