-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_classical_transposeRecovery
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.classical_transposeRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:18:46.632623+00:00
-- url     : https://prove2.me/theorems/27fce5d4-1a10-4669-9a2e-ecd792fe98fc
-- title:
--   Universal classical transpose recovery and deterministic equality
-- statement:
--   Fix a discrete probability law $Q$ on an arbitrary alphabet $X$ and a stochastic kernel $T:X\to U$. Define $R:X\leftarrow U$ by
--
--   $$R(x\mid u)=\frac{T(u\mid x)Q(x)}{(TQ)(u)}\quad\text{if }(TQ)(u)>0,$$
--
--   and take $R(\cdot\mid u)=Q$ otherwise. This one kernel depends only on $Q,T$, obeys $RTQ=Q$ and the Bayes relation $T(u\mid x)Q(x)=R(x\mid u)(TQ)(u)$, and for every probability law $P$ on $X$,
--
--   $$D_2(P\|Q)\ge D_2(TP\|TQ)+D_2(P\|RTP).$$
--
--   If $T$ is deterministic, equality holds. The divergences are extended nonnegative values in bits, so this additive form also handles infinite divergences without subtracting infinities. It is the sum form explicitly used in the proof on page 9.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 8, Lemma’ 1 / Eq.(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Lemma' 1, PDF pp.8–9, Eq.(17): the single Q,T-dependent transpose works
for every P, satisfies Bayes and recovers Q. Additive ENNReal form avoids infinity-minus-infinity;
deterministic T gives equality of this sum, including infinite divergences. -/
theorem classical_transposeRecovery {X U : Type*} (q : PMF X) (t : X → PMF U) :
    let r := transposeChannel q t
    (q.bind t).bind r = q ∧
      (∀ x u, t x u * q x = r u x * (q.bind t) u) ∧
      ∀ p : PMF X,
        discreteKL (p.bind t) (q.bind t) + discreteKL p ((p.bind t).bind r) ≤ discreteKL p q ∧
        ((∃ f : X → U, ∀ x, t x = PMF.pure (f x)) →
          discreteKL p q = discreteKL (p.bind t) (q.bind t) +
            discreteKL p ((p.bind t).bind r)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
