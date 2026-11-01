-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_bb84_coarse_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.bb84_coarse_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:24:02.990097+00:00
-- url     : https://prove2.me/theorems/3b9d5dd2-68ed-4aa5-a115-b0d26558b6e0
-- title:
--   Supplementary Note 6: classical reduction for BB84 sample errors
-- statement:
--   In the perfect single-photon qubit model, let $\rho$ be any normalized state of $N$ pairs. Fix any $m\le N$ distinct tested positions and any choice of the two matching BB84 bases $x,z$. Let $o$ record whether each pair's outcomes are parallel or antiparallel, and let $\mathcal D_{\rm Bell}$ be the complete nonselective $N$-Bell measurement. Then
--
--   $$\Pr_{\mathcal D_{\rm Bell}(\rho)}[o]=\Pr_\rho[o].$$
--
--   The equality holds jointly for all tested coarse outcomes, and hence also after averaging over independent random samples and bases. It does not claim preservation of the fine-grained polarization records.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 21, Supplementary Note 6: classical reduction for BB84 sample errors

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF p.21, second example: Bell premeasurement preserves the joint coarse error law
in the two matching BB84 bases, for every possible fixed test sample.
Averaging over an independent random test sample therefore preserves its law as well. -/
theorem bb84_coarse_reduction (N m : ℕ) (hm : m ≤ N)
    (rho : Matrix (PairRegister N) (PairRegister N) ℂ) (hrho : IsDensityMatrix rho)
    (s : Fin m ↪ Fin N) (axes : Fin m → Fin 3)
    (haxes : ∀ j, axes j = 0 ∨ axes j = 2) (anti : Qubits m) :
    pairAxisSampleLaw (bellPinch rho) s axes anti = pairAxisSampleLaw rho s axes anti := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
