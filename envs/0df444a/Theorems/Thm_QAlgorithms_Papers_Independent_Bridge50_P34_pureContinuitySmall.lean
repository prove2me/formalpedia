-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P34_pureContinuitySmall
-- name    : QAlgorithms.Papers.Independent.Bridge50.P34.pureContinuitySmall
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:05:57.197865+00:00
-- url     : https://prove2.me/theorems/17c15e4c-7d6e-4967-8995-177bffcf094a
-- title:
--   Pure-state entanglement continuity at small full trace distance
-- statement:
--   Let $\psi,\phi$ be unit vectors on finite complex systems $A\otimes B$, with positive dimensions $d,d'$. Set $E(\psi)=S(\operatorname{Tr}_B|\psi\rangle\langle\psi|)$, where $S$ is entropy in bits, and let $t=\operatorname{Tr}\bigl||\psi\rangle\langle\psi|-|\phi\rangle\langle\phi|\bigr|$. Put $\eta(x)=-x\log_2x$, with $\eta(0)=0$, and $e=\exp(1)$. If $t\le1/e$, then
--
--   $$
--   |E(\psi)-E(\phi)|\le t\min\{\log_2 d,\log_2 d'\}+\eta(t).
--   $$
--
--   The minimum expresses the bound with either subsystem chosen as $A$. The cutoff concerns the joint pure states, rather than only their reductions.
-- source:
--   Continuity bounds for entanglement, arXiv:quant-ph/9908086v2, PDF p. 2, Pure-state entanglement continuity with small full trace distance, (6)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P34

attribute [local instance] Classical.propDecidable Classical.decEq

-- Accepted definition providers, authorized by the independent-paper workflow.

open QAlgorithms.Papers.Independent.Information100.P08 (formation bellVector)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Support50.P42 (outcomeEntropy)

-- The supplied diagnostic timed out while elaborating the remote-control statement.

set_option maxHeartbeats 800000

/-- PDF p.2, (6), using the JOINT pure-state full trace distance. The minimum
retains the source's interchange of the two subsystems. -/
theorem pureContinuitySmall {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (psi phi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1)
    (hsmall : fullTraceDistance (pureDensity psi) (pureDensity phi) ≤ 1 / Real.exp 1) :
    |vnEntropy (traceRight (pureDensity psi)) - vnEntropy (traceRight (pureDensity phi))| ≤
      fullTraceDistance (pureDensity psi) (pureDensity phi) *
        min (Real.logb 2 (Fintype.card A)) (Real.logb 2 (Fintype.card B)) +
      (-(fullTraceDistance (pureDensity psi) (pureDensity phi)) *
        Real.logb 2 (fullTraceDistance (pureDensity psi) (pureDensity phi))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P34

end
