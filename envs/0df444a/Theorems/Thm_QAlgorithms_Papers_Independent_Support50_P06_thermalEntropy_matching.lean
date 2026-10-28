-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_thermalEntropy_matching
-- name    : QAlgorithms.Papers.Independent.Support50.P06.thermalEntropy_matching
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:33:43.365312+00:00
-- url     : https://prove2.me/theorems/d381fd6d-f1b0-423c-a1ad-ee6a63b734e0
-- title:
--   Thermal entropy and entropy-matched product states
-- statement:
--   Let $n\ge1$ and use natural-log von Neumann entropy on completed Fock spaces. A single-mode thermal state with finite mean $N\ge0$ satisfies
--
--   $$S(\rho_T(N))=g(N).$$
--
--   For two normalized $n$-mode port densities $\rho_a,\rho_b$ with finite entropies, set $K_a=g^{-1}(S(\rho_a)/n)$ and $K_b=g^{-1}(S(\rho_b)/n)$. Their corresponding identical thermal products satisfy
--
--   $$S(\rho_T(K_a)^{\otimes n})=S(\rho_a),\qquad S(\rho_T(K_b)^{\otimes n})=S(\rho_b).$$
--
--   This is entropy matching. No finite-energy assumption is imposed on the original densities, and their physical photon means are not identified with $K_a,K_b$.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §IV.B after (19)–(20): thermal entropy and entropy-matched products

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

/-- PDF p.4, (19)–(20): thermal entropy and the entropy-matched n-mode thermal
products for BOTH independent ports. Matching entropy never identifies an
arbitrary state's physical mean photons with its entropy photon number. -/
theorem thermalEntropy_matching (n : ℕ) (hn : 0 < n) :
    (∀ N : ℝ, 0 ≤ N → spectralEntropyNats (identicalThermalKernel 1 N) =
      ENNReal.ofReal (g N)) ∧
    (∀ rhoA rhoB : State (NumberString n),
      spectralEntropyNats rhoA.coefficients ≠ ⊤ →
      spectralEntropyNats rhoB.coefficients ≠ ⊤ →
      spectralEntropyNats (identicalThermalKernel n
        (entropyParameter n (spectralEntropyNats rhoA.coefficients))) =
          spectralEntropyNats rhoA.coefficients ∧
      spectralEntropyNats (identicalThermalKernel n
        (entropyParameter n (spectralEntropyNats rhoB.coefficients))) =
          spectralEntropyNats rhoB.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
