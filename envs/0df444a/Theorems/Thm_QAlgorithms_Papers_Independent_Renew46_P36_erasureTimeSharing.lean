-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_erasureTimeSharing
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.erasureTimeSharing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:07:40.626012+00:00
-- url     : https://prove2.me/theorems/6ef08bef-d2ec-4984-8424-949b31fa23b1
-- title:
--   §2: optimal time-sharing for an erasure channel
-- statement:
--   Let $A'$ be a finite nonzero complex register, let $p\in[0,1]$, and let $|e\rangle$ be an orthogonal erasure flag. Define the erasure channel on all input operators by $\mathcal E_p(X)=(1-p)X\oplus p\operatorname{Tr}(X)|e\rangle\langle e|$. Write $C(\mathcal E_p)$ for the operational classical capacity and $Q(\mathcal E_p)$ for the operational unassisted entanglement-transmission capacity. In any of scenarios Ia, Ib, or II, the nonnegative simultaneous capacity region is exactly
--
--   $$
--   S_s(\mathcal E_p)=\{(r,R)\geq0:\exists t\in[0,1],\ r\leq tC(\mathcal E_p),\ R\leq(1-t)Q(\mathcal E_p)\}.
--   $$
--
--   Time-sharing is therefore optimal for this channel. This statement includes a one-dimensional input and zero quantum capacity, and does not assume the separately cited formulas for the two individual capacities.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 5, §2: optimal time-sharing for an erasure channel

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Section 2, PDF p.5: simultaneous optimality of erasure-channel time-sharing.
The separate erasure capacity formulas are cited background, not assumed here.
The orthogonal flag and division-free triangle retain d=1 and Q=0. -/
theorem erasureTimeSharing [Nonempty A] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Scenario) :
    simultaneousOperationalRegion s (flaggedErasure (A := A) p) =
      sharingTriangle (operationalClassicalAxisCapacity (flaggedErasure (A := A) p))
        (quantumCapacity (flaggedErasure (A := A) p)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
