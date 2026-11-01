-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P49_cloningComplement_entanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P49.cloningComplement_entanglementBreaking
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:24:58.303986+00:00
-- url     : https://prove2.me/theorems/79974ba0-f218-4e4b-ad4c-6afe146a4fa1
-- title:
--   Lemma 1: complementary cloning channels are entanglement breaking
-- statement:
--   For every integer $\ell\ge2$, let $S^c_{\ell-1}$ be the complementary channel obtained by tracing out the receiver of the same isometry that defines $\mathrm{Cl}_{1,\ell-1}$. Its output dimension is $\ell-1$. It is CPTP and entanglement breaking:
--
--   $$
--   (\operatorname{id}_R\otimes S^c_{\ell-1})(\rho_{RA})\ \text{is separable}
--   $$
--
--   for every normalized bipartite density operator with qubit system $A$ and arbitrary positive finite reference $R$. At $\ell=2$ the complement is the scalar trace map. This property identifies the complementary cloning family as entanglement breaking, without assuming separability as an input hypothesis.
--
--   **Formalization Note** The accepted predicate tests normalized pure states with an input-sized reference; for CPTP maps, Schmidt decomposition and convexity give the displayed formulation. The inconsistent Eq. (15) is not used to define the channel.
-- source:
--   An Infinite Sequence of Additive Channels: the Classical Capacity of Cloning Channels, arXiv:0903.1638v7, PDF p. 4, Lemma 1

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

/-- PDF p.4, Lemma 1: every genuine complementary cloning channel is
entanglement breaking, including the ell=2 trace map. -/
theorem cloningComplement_entanglementBreaking (k : ℕ) :
    IsChannel (clonerComplement k) ∧
    EntanglementBreaking (by omega) (by omega) (clonerComplement k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P49

end
