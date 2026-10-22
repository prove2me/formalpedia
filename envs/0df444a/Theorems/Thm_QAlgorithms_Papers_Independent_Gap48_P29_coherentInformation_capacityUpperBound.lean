-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_coherentInformation_capacityUpperBound
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.coherentInformation_capacityUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:27:44.486147+00:00
-- url     : https://prove2.me/theorems/3cd6ed64-818c-49d0-b539-894e107547a4
-- title:
--   Regularized coherent-information upper bound on capacity
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. For a block input density operator $\rho$, define $I_c(\rho,\mathcal N^{\otimes n})=S(\mathcal N^{\otimes n}(\rho))-S((\mathrm{id}\otimes\mathcal N^{\otimes n})(|\Psi_\rho\rangle\langle\Psi_\rho|))$, where $\Psi_\rho$ is a purification and entropy is in bits. The following limit exists as a finite real number and bounds the QAEP-source quantum capacity:
--
--   $$Q_e(\mathcal N)\leq\lim_{n\to\infty}\frac1n\max_{\rho\text{ a block input density}}I_c(\rho,\mathcal N^{\otimes n}).$$
--
--   The maximization includes entangled block inputs and uses positive block lengths. Only an upper bound is claimed.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 12, Section IX, Eq.(113), p.12

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF pp.11--12, Eq.(113): existence of the finite regularized block-maximum
limit and its upper bound on capacity. The block index is n+1, so every optimized
channel uses a positive number of copies. No equality with this bound is claimed. -/
theorem coherentInformation_capacityUpperBound {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N) :
    ∃ L : ℝ,
      Tendsto (fun n : ℕ => coherentBlockMaximum N (n + 1) / (n + 1 : ℕ))
        atTop (nhds L) ∧ qe N ≤ L := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
