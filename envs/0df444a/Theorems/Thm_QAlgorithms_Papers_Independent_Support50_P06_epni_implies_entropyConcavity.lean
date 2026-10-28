-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_epni_implies_entropyConcavity
-- name    : QAlgorithms.Papers.Independent.Support50.P06.epni_implies_entropyConcavity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:35:43.646886+00:00
-- url     : https://prove2.me/theorems/40cf705f-f6ad-4835-a4f9-a35ee7048e3a
-- title:
--   Pointwise EPnI implies linear entropy concavity
-- statement:
--   Let $n\ge1$ and $0\le\eta\le1$. Mix independent normalized $n$-mode port densities $\rho_a,\rho_b$ of finite entropies with retained output $\rho_c$, using the source's full-space beam splitter. Assume the pointwise EPnI $\mathcal N(\rho_c)\ge\eta\mathcal N(\rho_a)+(1-\eta)\mathcal N(\rho_b)$, where $\mathcal N(\rho)=g^{-1}(S(\rho)/n)$ and infinite output entropy is assigned infinite entropy photon number. Then
--
--   $$S(\rho_c)\ge\eta S(\rho_a)+(1-\eta)S(\rho_b).$$
--
--   The output entropy may be infinite. This is the implication proved in note [14]; no converse is asserted.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §V, (22) implies (24), proof in note [14]

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

/-- PDF pp.4–5, (24), note [14], (30)–(32): pointwise EPnI implies the
linear entropy bound. No converse or unconditional EPnI is asserted. -/
theorem epni_implies_entropyConcavity (n : ℕ) (hn : 0 < n) (eta : ℝ)
    (heta : 0 ≤ eta) (heta_one : eta ≤ 1) (rhoA rhoB : State (NumberString n))
    (hA : spectralEntropyNats rhoA.coefficients ≠ ⊤)
    (hB : spectralEntropyNats rhoB.coefficients ≠ ⊤)
    (hepni : EpniAt eta rhoA.coefficients rhoB.coefficients) :
    ENNReal.ofReal eta * spectralEntropyNats rhoA.coefficients +
        ENNReal.ofReal (1 - eta) * spectralEntropyNats rhoB.coefficients ≤
      spectralEntropyNats (mixedOutput n eta rhoA.coefficients rhoB.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
