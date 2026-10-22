-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_lowerEntropySource_transmissible
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.lowerEntropySource_transmissible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:18:21.242277+00:00
-- url     : https://prove2.me/theorems/6ec08116-0bc1-47c8-9772-8c99c68df31a
-- title:
--   Every lower-entropy QAEP source can be transmitted
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. Let $C(\mathcal N)=Q_e(\mathcal N)=Q_s(\mathcal N)$ be the common operational capacity. If $s<C(\mathcal N)$, there is a sequence of physical encoders $\mathcal E_n$ and decoders $\mathcal D_n$ such that
--
--   $$\lim_{n\to\infty}F_e(\rho_n,\mathcal D_n\mathcal N^{\otimes n}\mathcal E_n)=1.$$
--
--   This is the source-channel transmission consequence for every QAEP source below capacity.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 9, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.9, Theorem 3: source-channel transmission for every lower-entropy QAEP
source; C(N) is the common operational capacity, not a single-letter formula. -/
theorem lowerEntropySource_transmissible {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N)
    (S : BlockQuantumSource) (hS : QAEP S) (hrate : sourceEntropyRate S < qe N) : Transmissible S N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
