-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_projectiveRobustness_fidelity_ceiling
-- name    : QAlgorithms.Papers.Independent.Information100.P06.projectiveRobustness_fidelity_ceiling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:29:19.16899+00:00
-- url     : https://prove2.me/theorems/8f73fe52-260d-47d4-9aec-611bb0bb8632
-- title:
--   Proposition 13: fidelity ceiling from projective robustness
-- statement:
--   Let A and B be finite-dimensional complex dynamical systems with positive input and output dimensions. Represent each CPTP channel N by its normalized Choi matrix J_N, with the input index first. Let F_A and F_B be nonempty sets of free CPTP channels. A successful physical superinstrument branch is completely CP preserving and completely CPTNI preserving, belongs to a two-outcome superinstrument whose sum is completely CPTP preserving, and sends every free channel into the nonnegative cone of free channels, including the zero branch. Suppose its action on N is p N', where p>0 is independent of the transmitted state and N' is CPTP.
--
--   Let Phi be any CPTP target, write <N',Phi>=Tr(J_N' J_Phi), and put c=sup_{M in F_B} Tr(J_M J_Phi) and r=Omega_{F_A}(N). For finite r and 0<c<1,
--   $$
--   \langle N',\Phi\rangle\le \frac{rc}{rc+1-c}.
--   $$
--   The ceiling is 1 if r is infinite or c=1, and is 0 if r is finite and c=0. Here all traces of products of Hermitian matrices are real. No purity assumption is made on Phi. This gives an overlap ceiling even for inputs with singular Choi matrices.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 14, Proposition 13: fidelity ceiling from projective robustness

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF p.14, Proposition 13: resource-distillation overlap ceiling, including
rank-deficient inputs and the free-overlap endpoints zero and one. -/
theorem projectiveRobustness_fidelity_ceiling
    {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (N : Choi A0 A1) (Nout Phi : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (hPhi : IsChannelChoi Phi)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    QAlgorithms.effectProb Nout Phi ≤ fidelityCeiling (projectiveRobustness F N) (freeOverlap G Phi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
