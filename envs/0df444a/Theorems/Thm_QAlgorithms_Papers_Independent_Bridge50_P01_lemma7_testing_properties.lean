-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P01_lemma7_testing_properties
-- name    : QAlgorithms.Papers.Independent.Bridge50.P01.lemma7_testing_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:33:08.498611+00:00
-- url     : https://prove2.me/theorems/3974633a-609c-4489-bdce-107e6a1fa191
-- title:
--   Four properties of hypothesis-testing relative entropy
-- statement:
--   Let $0<\varepsilon<1$ and let all Hilbert spaces be finite dimensional and nonzero. For a density matrix $\rho$ and a positive semidefinite operator $\sigma$, define
--
--   $$
--   D_H^\varepsilon(\rho\Vert\sigma)=-\log_2\min\{\operatorname{Tr}(Q\sigma):0\le Q\le I,\ \operatorname{Tr}(Q\rho)\ge1-\varepsilon\}.
--   $$
--
--   A zero minimum gives $+\infty$. Then:
--
--   1. For $\sigma'\ge\sigma\ge0$, $D_H^\varepsilon(\rho\Vert\sigma)\ge D_H^\varepsilon(\rho\Vert\sigma')$.
--   2. For $\alpha>0$, $D_H^\varepsilon(\rho\Vert\alpha\sigma)=D_H^\varepsilon(\rho\Vert\sigma)-\log_2\alpha$.
--   3. For any finite nonempty alphabet $X$, independently chosen probability distributions $p,q$, conditional density matrices $\rho_B^x$, and density matrix $\sigma_B$, put $\rho_{XB}=\sum_xp(x)|x\rangle\langle x|\otimes\rho_B^x$ and $\sigma_X=\sum_xq(x)|x\rangle\langle x|$. Then
--
--   $$
--   D_H^\varepsilon(\rho_{XB}\Vert\sigma_X\otimes\sigma_B)\ge\min_xD_H^\varepsilon(\rho_B^x\Vert\sigma_B).
--   $$
--
--   4. If $0<\delta<1-\varepsilon$ and $\rho,\rho'$ are densities with $\|\rho-\rho'\|_1/2\le\delta$, then $D_H^\varepsilon(\rho'\Vert\sigma)\le D_H^{\varepsilon+\delta}(\rho\Vert\sigma)$ for every positive semidefinite $\sigma$.
--
--   These properties control comparison states, scaling, classical conditioning, and perturbations in the one-shot analysis.
-- source:
--   On the Second-Order Asymptotics for Entanglement-Assisted Communication, arXiv:1405.1797v2, PDF p. 7, Lemma 7, pp.7–8

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P01

open QAlgorithms Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

-- Reuse pinned accepted definitions; these are not other draft chunks.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

open QAlgorithms.Papers.Independent.Frontier30.P01 (classicalState)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7–8, Lemma 7: all four properties, including arbitrary p and q
in the cq comparison and an unnormalized, possibly zero, PSD alternative. -/
theorem lemma7_testing_properties (epsilon : ℝ) (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (rho sigma sigmaLarge : Op I),
      IsDensityMatrix rho → sigma.PosSemidef → (sigmaLarge - sigma).PosSemidef →
      testingD epsilon rho sigmaLarge ≤ testingD epsilon rho sigma) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (rho sigma : Op I) (alpha : ℝ),
      IsDensityMatrix rho → sigma.PosSemidef → 0 < alpha →
      testingD epsilon rho ((alpha : ℂ) • sigma) =
        testingD epsilon rho sigma - (log2 alpha : EReal)) ∧
    (∀ (X B : Type) [Fintype X] [Fintype B] [DecidableEq X] [DecidableEq B]
      [Nonempty X] [Nonempty B] (p q : X → ℝ) (rho : X → Op B) (sigma : Op B),
      (∀ x, 0 ≤ p x) → (∑ x, p x) = 1 →
      (∀ x, 0 ≤ q x) → (∑ x, q x) = 1 →
      (∀ x, IsDensityMatrix (rho x)) → IsDensityMatrix sigma →
      (Finset.univ.inf (fun x => testingD epsilon (rho x) sigma)) ≤
        testingD epsilon (cqState p rho) (Matrix.kronecker (classicalState q) sigma)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (rho rhoNear sigma : Op I) (delta : ℝ),
      0 < delta → delta < 1 - epsilon → IsDensityMatrix rho → IsDensityMatrix rhoNear →
      traceNorm (rho - rhoNear) / 2 ≤ delta → sigma.PosSemidef →
      testingD epsilon rhoNear sigma ≤ testingD (epsilon + delta) rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P01

end
