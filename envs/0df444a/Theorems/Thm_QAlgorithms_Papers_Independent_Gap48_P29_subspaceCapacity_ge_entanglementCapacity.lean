-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_subspaceCapacity_ge_entanglementCapacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.subspaceCapacity_ge_entanglementCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:16:09.966367+00:00
-- url     : https://prove2.me/theorems/f40e29b8-8c32-4430-ab52-40c814c9ddf3
-- title:
--   Entanglement transmission implies subspace transmission
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. Write $Q_e(\mathcal N)$ for the supremum of entropy rates of reliably transmitted QAEP sources, and $Q_s(\mathcal N)$ for the supremum of reliably transmitted subspace rates, measured using minimum squared pure-state fidelity. Source entropy rate and subspace rate use the limsup per channel use, with entropy and logarithms in bits. Then
--
--   $$Q_s(\mathcal N)\geq Q_e(\mathcal N).$$
--
--   Thus a rate available for entanglement transmission can be approached using subspaces with uniformly high pure-state fidelity.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 8, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.8, Theorem 1: entanglement transmission gives subspace capacity. -/
theorem subspaceCapacity_ge_entanglementCapacity {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N) : qe N ≤ qs N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
