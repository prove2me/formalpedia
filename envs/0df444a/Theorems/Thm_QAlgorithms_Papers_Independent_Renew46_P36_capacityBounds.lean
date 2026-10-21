-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_capacityBounds
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.capacityBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:05:39.271007+00:00
-- url     : https://prove2.me/theorems/7dd1b69e-13b8-437a-b56b-457e43a1c859
-- title:
--   §2: time-sharing inner bound and classical outer bound
-- statement:
--   Let $\mathcal N:A'\to B$ be a CPTP map on finite nonzero registers, and let $S_s(\mathcal N)$ be its unassisted simultaneous capacity region in any of scenarios Ia, Ib, or II, with every-message correctness, squared fidelity, and arbitrarily small error and rate slack at every sufficiently large positive block length. Define $C(\mathcal N)$ operationally as the supremum of the achievable classical-axis rates in Ia. Define $Q(\mathcal N)$ independently by asymptotic CPTP entanglement-transmission encoders and decoders on all tensor powers. Both capacities are finite and nonnegative, and both axis endpoints belong to $S_s(\mathcal N)$.
--
--   For nonnegative $C,Q$ define the downward triangle $T(C,Q)=\{(r,R)\geq0:\exists t\in[0,1],\ r\leq tC,\ R\leq(1-t)Q\}$. Then
--
--   $$
--   (C(\mathcal N),0),(0,Q(\mathcal N))\in S_s(\mathcal N),\qquad
--   T(C(\mathcal N),Q(\mathcal N))\subseteq S_s(\mathcal N)
--   \subseteq\{(r,R)\geq0:r+R\leq C(\mathcal N)\}.
--   $$
--
--   These are full downward inner and outer bounds. The definition of $T$ remains meaningful when a capacity vanishes and uses no division by $Q$.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 4, §2: time-sharing inner bound and classical outer bound

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

/-- Section 2, PDF p.4: the full downward inner triangle and outer triangle,
with independently operational classical and quantum capacities, and both endpoints. -/
theorem capacityBounds
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) (s : Scenario) :
    0 ≤ operationalClassicalAxisCapacity N ∧ 0 ≤ quantumCapacity N ∧
    (operationalClassicalAxisCapacity N, 0) ∈ simultaneousOperationalRegion s N ∧
    (0, quantumCapacity N) ∈ simultaneousOperationalRegion s N ∧
    sharingTriangle (operationalClassicalAxisCapacity N) (quantumCapacity N) ⊆ simultaneousOperationalRegion s N ∧
    simultaneousOperationalRegion s N ⊆ {v : ℝ × ℝ | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 + v.2 ≤ operationalClassicalAxisCapacity N} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
