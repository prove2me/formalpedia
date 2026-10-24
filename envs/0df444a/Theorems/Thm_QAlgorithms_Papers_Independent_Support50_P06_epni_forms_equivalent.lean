-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_epni_forms_equivalent
-- name    : QAlgorithms.Papers.Independent.Support50.P06.epni_forms_equivalent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:34:55.175018+00:00
-- url     : https://prove2.me/theorems/fd08aaac-65df-4ac2-8ca9-29ae2ae53ece
-- title:
--   Equivalence of the two pointwise EPnI forms
-- statement:
--   Let $n\ge1$, $0\le\eta\le1$, and let $\rho_a,\rho_b$ be arbitrary normalized $n$-mode densities with finite entropies, independent across the two input ports. Correlations within each port are allowed. Let $\rho_c$ be the actual retained output of $c=\sqrt\eta\,a+\sqrt{1-\eta}\,b$. Define $\mathcal N(\rho)=g^{-1}(S(\rho)/n)$ for finite entropy and extend it to $+\infty$ for infinite output entropy. Put $K=\eta\mathcal N(\rho_a)+(1-\eta)\mathcal N(\rho_b)$. Then
--
--   $$\mathcal N(\rho_c)\ge K\quad\Longleftrightarrow\quad S(\rho_c)\ge S(\rho_T(K)^{\otimes n}).$$
--
--   This proves equivalence of the two conjectured inequalities, rather than either inequality unconditionally. Infinite output entropy satisfies both forms automatically; no input-energy bound is added.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §IV.B, (22) iff (23), proof in bibliography note [13]

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (22) iff (23); both directions proved in note [13], p.5.
This equivalence does not assert EPnI. Infinite output entropy satisfies both
sides; input entropies are finite so the comparison thermal state is defined. -/
theorem epni_forms_equivalent (n : ℕ) (hn : 0 < n) (eta : ℝ)
    (heta : 0 ≤ eta) (heta_one : eta ≤ 1) (rhoA rhoB : State (NumberString n))
    (hA : spectralEntropyNats rhoA.coefficients ≠ ⊤)
    (hB : spectralEntropyNats rhoB.coefficients ≠ ⊤) :
    EpniAt eta rhoA.coefficients rhoB.coefficients ↔
      spectralEntropyNats (identicalThermalKernel n
        (eta * entropyParameter n (spectralEntropyNats rhoA.coefficients) +
          (1 - eta) * entropyParameter n (spectralEntropyNats rhoB.coefficients))) ≤
        spectralEntropyNats (mixedOutput n eta rhoA.coefficients rhoB.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
