-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_cloning_strongAdditivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.cloning_strongAdditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:23:55.162928+00:00
-- url     : https://prove2.me/theorems/3f789028-f24e-4fa8-aa27-97bed3fdf2df
-- title:
--   Theorem 1: strong Holevo additivity of every 1-to-(ell-1) qubit cloning channel
-- statement:
--   Let $\ell\ge2$ be an integer and let $\mathrm{Cl}_{1,\ell-1}$ be the universal symmetric qubit cloning channel whose receiver holds all $\ell-1$ clones in their $\ell$-dimensional symmetric subspace. The channel is the receiver reduction of the occupation-basis isometry in Eqs. (9)–(11). For every CPTP auxiliary channel $T$ between arbitrary positive finite dimensions,
--
--   $$
--   \chi(\mathrm{Cl}_{1,\ell-1}\otimes T)=\chi(\mathrm{Cl}_{1,\ell-1})+\chi(T).
--   $$
--
--   Here $\chi(N)$ is the supremum of the Holevo information over all finite ensembles of positive trace-one input operators, with entropy in bits. Joint inputs to the tensor product may be mixed and entangled. This is strong additivity and gives the classical single-letter property of the complete cloning output.
--
--   **Formalization Note** The natural parameter is $k=\ell-2$. CPTP is included in the additivity predicate. The PDF's Eq. (9) agrees with the accepted dilation; the plan's claim of overlapping images at $k=0$ is contradicted by the original page.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 3, Theorem 1

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

/-- PDF p.3, Theorem 1 (proof p.4): strong Holevo additivity for every ell>=2.
The occupation-basis dilation agrees with Eqs.(9)--(11); Eq.(15) is not used. -/
theorem cloning_strongAdditivity (k : ℕ) : StrongHolevoAdditive (cloner k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
