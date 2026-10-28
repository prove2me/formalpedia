-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_source_partialEncodings
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.source_partialEncodings
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:26:14.151785+00:00
-- url     : https://prove2.me/theorems/987daf0f-c87d-4478-8cec-e477159d2463
-- title:
--   Source-specific sufficiency of partial encodings
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. Let $\Sigma=\{\rho_n\}$ be any source on tensor powers of one nonzero finite-dimensional space; QAEP is not required. Suppose encoders $\mathcal E_n$ and decoders $\mathcal D_n$ transmit it reliably. There exist partial isometries $W_n$ and CP completion branches $\mathcal G_n$ such that $\mathcal F_n(X)=W_nXW_n^\dagger+\mathcal G_n(X)$ is trace preserving and
--
--   $$F_e(\rho_n,\mathcal D_n\mathcal N^{\otimes n}[W_n(\cdot)W_n^\dagger])\to1,\qquad F_e(\rho_n,\mathcal D_n\mathcal N^{\otimes n}\mathcal F_n)\to1.$$
--
--   The same decoders are retained. The partial-isometry branch itself may decrease trace.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 11, Consequence of Theorem 4, pp.10–11

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF pp.10--11, consequence of Theorem 4 (also p.11, section IX): every reliable
source-specific code admits partial-isometry branches and physical TP completions,
with the SAME decoders. No QAEP assumption is required for this statement. -/
theorem source_partialEncodings {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N)
    (S : BlockQuantumSource) (C : SourceTransmissionCode S c o) (hgood : Reliable N C) :
    ∃ W : (n : ℕ) → Matrix (SourceRegister c n) (SourceRegister S.dimension n) ℂ,
      ∃ G : (n : ℕ) → Superop (SourceRegister S.dimension n) (SourceRegister c n),
        (∀ n, IsPartialIsometry (W n) ∧ FiniteCPMap (G n) ∧
          IsChannel (fun X => conjSuperop (W n) X + G n X)) ∧
        Tendsto (fun n => fe (S.rho n)
          (C.dec n ∘ piSuperop (fun _ : Fin n => N) ∘ conjSuperop (W n))) atTop (nhds 1) ∧
        Tendsto (fun n => fe (S.rho n)
          (C.dec n ∘ piSuperop (fun _ : Fin n => N) ∘
            (fun X => conjSuperop (W n) X + G n X))) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
