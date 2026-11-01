-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_cloning_degradable
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.cloning_degradable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:25:49.281767+00:00
-- url     : https://prove2.me/theorems/56384da5-66a3-4d98-91eb-9035ea8483a8
-- title:
--   Corollary 1: every cloning channel is degradable
-- statement:
--   For every integer $\ell\ge2$, the cloning channel $\mathrm{Cl}_{1,\ell-1}$ is degradable. There exists one CPTP map $D_\ell$ from the $\ell$-dimensional cloning output to the $(\ell-1)$-dimensional environment such that
--
--   $$
--   D_\ell\circ\mathrm{Cl}_{1,\ell-1}=S^c_{\ell-1}.
--   $$
--
--   The complement is defined by the same fixed occupation-basis isometry. The equality holds on all input operators, so the degrading map works uniformly for all mixed and entangled inputs. This is ordinary degradability of the concrete cloning channel.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 4, Corollary 1

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

/-- PDF p.4, Corollary 1: a single CPTP degrading map works for every input. -/
theorem cloning_degradable (k : ℕ) : IsDegradable (unruhSectorDilation k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
