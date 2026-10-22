-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_capacities_equal
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.capacities_equal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:10:00.52224+00:00
-- url     : https://prove2.me/theorems/d761dab3-7016-495f-b256-b96c54dddcf4
-- title:
--   Entanglement and minimum-subspace capacities coincide
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. Write $Q_e(\mathcal N)$ for the supremum of entropy rates of reliably transmitted QAEP sources, and $Q_s(\mathcal N)$ for the supremum of reliably transmitted subspace rates, measured using minimum squared pure-state fidelity. Source entropy rate and subspace rate use the limsup per channel use, with entropy and logarithms in bits. Then
--
--   $$Q_e(\mathcal N)=Q_s(\mathcal N).$$
--
--   This identifies the two operational transmission criteria within the QAEP source class. It does not identify capacity with a single-letter coherent-information expression.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 1, Abstract; Theorem 1 and Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.1 abstract; pp.8--9, Theorem 1 and Corollary 1: equivalence of the two
operational capacities, within the QAEP source class. -/
theorem capacities_equal {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N) : qe N = qs N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
