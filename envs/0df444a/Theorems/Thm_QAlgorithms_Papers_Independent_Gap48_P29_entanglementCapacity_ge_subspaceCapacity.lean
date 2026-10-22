-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_entanglementCapacity_ge_subspaceCapacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.entanglementCapacity_ge_subspaceCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:17:35.042628+00:00
-- url     : https://prove2.me/theorems/faf04983-59b1-476b-a9fc-d5224df2afa3
-- title:
--   Subspace transmission implies entanglement transmission
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. Write $Q_e(\mathcal N)$ for the supremum of entropy rates of reliably transmitted QAEP sources, and $Q_s(\mathcal N)$ for the supremum of reliably transmitted subspace rates, measured using minimum squared pure-state fidelity. Source entropy rate and subspace rate use the limsup per channel use, with entropy and logarithms in bits. Then
--
--   $$Q_e(\mathcal N)\geq Q_s(\mathcal N).$$
--
--   Moreover, for any sequence of nonzero subspace projectors $P_n$ and trace-preserving transmission operations $\mathcal A_n$, minimum pure-state fidelity tending to one on their ranges implies
--
--   $$\lim_{n\to\infty}F_e\!\left(\frac{P_n}{\dim\operatorname{ran}P_n},\mathcal A_n\right)=1.$$
--
--   The latter assertion uses the same operations; it does not impose QAEP on an arbitrary oscillating subspace family.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 9, Corollary 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.9, Corollary 1: reverse capacity inequality, together with the stated
same-operation reliability of uniform density operators on transmitted subspaces.
The latter conclusion itself does not impose a regular-rate/QAEP condition. -/
theorem entanglementCapacity_ge_subspaceCapacity {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N) :
    qs N ≤ qe N ∧
    ∀ (d : ℕ), 0 < d →
      ∀ (P : (n : ℕ) → Matrix (SourceRegister d n) (SourceRegister d n) ℂ)
        (A : (n : ℕ) → Superop (SourceRegister d n) (SourceRegister d n)),
        (∀ n, IsProjection (P n) ∧ 0 < projectionDimension (P n)) →
        (∀ n, IsChannel (A n)) → SubspaceReliable P A →
        Tendsto (fun n => fe (uniformOn (P n)) (A n)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
