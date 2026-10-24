-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_epni_implies_moe1
-- name    : QAlgorithms.Papers.Independent.Support50.P06.epni_implies_moe1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:36:21.66025+00:00
-- url     : https://prove2.me/theorems/441701e4-909a-46dd-9082-a36ae10a0181
-- title:
--   EPnI implies the centered-pure-input vacuum minimizer
-- statement:
--   Assume EPnI for every positive number of modes, every transmissivity in $[0,1]$, and every pair of independent normalized input port densities with finite input entropies. Let $n\ge1$, $0\le\eta\le1$ and finite $K\ge0$. Let the $a$ input be any normalized pure $n$-mode state whose annihilation-field expectation in each mode exists and is zero, and let the independent $b$ input be $\rho_T(K)^{\otimes n}$. Then
--
--   $$S(\rho_c)\ge n g((1-\eta)K).$$
--
--   The vacuum $a$ input attains this minimum: its actual output is $\rho_T((1-\eta)K)^{\otimes n}$ and has exactly the displayed entropy. No finite-photon-energy or Gaussian assumption is imposed on the optimized pure input. The formal centered predicate uses convergent sums, rather than interpreting a divergent sum as zero.
--
--   Thus global EPnI implies minimum output entropy conjecture 1 with its attained value.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §V, Minimum Output Entropy Conjecture 1 as a consequence of EPnI

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

/-- PDF pp.4–5, Conjecture 1 and (25): a conditional implication with the
vacuum attained value n*g((1-eta)*K). Pure means norm one; centered means
convergent annihilation expectations, with no finite-energy restriction. -/
theorem epni_implies_moe1 (hepni : EntropyPhotonNumberInequality) :
    MinimumOutputEntropyConjecture1 := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
