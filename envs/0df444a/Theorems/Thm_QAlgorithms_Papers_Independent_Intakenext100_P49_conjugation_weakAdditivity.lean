-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_conjugation_weakAdditivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.conjugation_weakAdditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:27:26.124+00:00
-- url     : https://prove2.me/theorems/7f8288fd-7428-4b49-8dd8-1834304d1263
-- title:
--   Lemma 2: weak additivity after output complex conjugation
-- statement:
--   Let $N$ be a CPTP channel between positive finite-dimensional Hilbert spaces. Assume its Holevo capacity is weakly additive, meaning $\chi(N^{\otimes n})=n\chi(N)$ for every positive integer $n$; a strongly additive channel also meets this premise. In a fixed output basis let $M$ be the linear map $M(X)=N(X)^T$, and assume explicitly that $M$ is CPTP. Then
--
--   $$
--   \chi(M^{\otimes n})=n\chi(M)\qquad(n\ge1).
--   $$
--
--   Transpose agrees with entrywise complex conjugation on Hermitian density operators. This gives weak additivity of the conjugated channel when that channel exists in the CP sense required by the source's p.5 remark. It does not assert strong additivity of $M$.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 4, Lemma 2 (continued p.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P49

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Support50.P01
  (unruhSectorDilation unruhWeight unruhBlockDilation unruhBlockWeight
   unruhReceiver unruhReceiverEntropy)

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open QAlgorithms.Papers.Independent.Dependency50.P45 (holevoCapacity)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.QuditFidelity (depolarizingMap)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4--5, Lemma 2 and its CP remark: weak additivity survives
output conjugation when the transpose extension is itself CPTP.
Weak additivity is the minimal premise and covers a strongly additive N as well. -/
theorem conjugation_weakAdditivity (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : WeakHolevoAdditive N)
    (hM : IsChannel (transposeOutput N)) : WeakHolevoAdditive (transposeOutput N) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
