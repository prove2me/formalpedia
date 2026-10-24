-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_epni_implies_moe2
-- name    : QAlgorithms.Papers.Independent.Support50.P06.epni_implies_moe2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:37:01.651763+00:00
-- url     : https://prove2.me/theorems/30563d67-f08d-4ff8-a25a-b7cb3789884b
-- title:
--   EPnI implies the fixed-entropy thermal minimizer
-- statement:
--   Assume global EPnI on the finite-input-entropy domain. Let $n\ge1$, $0\le\eta\le1$, and finite $K\ge0$. The $a$ input is vacuum and the independent $b$ input is any normalized $n$-mode density satisfying the entropy shell $S(\rho_b)=ng(K)$. Then
--
--   $$S(\rho_c)\ge n g((1-\eta)K).$$
--
--   The identical thermal product $\rho_T(K)^{\otimes n}$ has input entropy $ng(K)$ and attains equality at the output. The result is global over all these parameters and all states on the shell; it imposes no Gaussian or finite-energy restriction.
--
--   This is precisely the accepted StrongConjecture2 predicate, used here as a conditional conclusion, not an established unconditional premise.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §V, Minimum Output Entropy Conjecture 2 as a consequence of EPnI

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

/-- PDF pp.4–5, Conjecture 2, (26): EPnI implies the global accepted MOE2
predicate, including thermal attainment. The shell is S(rho)=n*g(K); neither
Gaussianity nor a mean-photon constraint is imposed on rho. -/
theorem epni_implies_moe2 (hepni : EntropyPhotonNumberInequality) :
    StrongConjecture2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
