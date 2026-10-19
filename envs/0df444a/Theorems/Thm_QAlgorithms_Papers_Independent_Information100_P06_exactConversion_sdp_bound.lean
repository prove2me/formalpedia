-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_exactConversion_sdp_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P06.exactConversion_sdp_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:30:42.710476+00:00
-- url     : https://prove2.me/theorems/9e5d8228-646e-4dd6-9186-e6fc521450ff
-- title:
--   Theorem 15: SDP upper bound for exact probabilistic conversion
-- statement:
--   Let A and B be finite-dimensional complex dynamical systems with positive input and output dimensions. Represent each CPTP channel N by its normalized Choi matrix J_N, with the input index first. Let F_A and F_B be nonempty sets of free CPTP channels. A successful physical superinstrument branch is completely CP preserving and completely CPTNI preserving, belongs to a two-outcome superinstrument whose sum is completely CPTP preserving, and sends every free channel into the nonnegative cone of free channels, including the zero branch. Suppose its action on N is p N', where p>0 is independent of the transmitted state and N' is CPTP.
--
--   Assume F_A and F_B are convex. Write d=dim(A_0), let Pi_{J_N'} be the orthogonal projection onto the support of J_N', and set v=sup_{M in F_B} Tr(Pi_{J_N'} J_M). Define Xi as the maximum of Tr(W J_N), over Hermitian W,Z and a density matrix sigma on A_0, subject to
--   $$
--   0\preceq W\preceq Z\preceq d\,\sigma\otimes I_{A_1},\qquad
--   \operatorname{Tr}(WJ_N)=\operatorname{Tr}(ZJ_N),
--   $$
--   $$
--   \operatorname{Tr}(WJ_M)\le v\operatorname{Tr}(ZJ_M)\quad\text{for every }M\in F_A.
--   $$
--   Then p<=Xi, and the displayed maximum is attained. The input and output free sets have distinct roles. This SDP bounds the probability of exact conversion.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 15, Theorem 15: SDP upper bound for exact probabilistic conversion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF p.15, Theorem 15: SDP ceiling for exact conversion in a convex
resource theory. Input and output free sets are distinct; the supremum is
attained, so the statement retains the printed maximum. -/
theorem exactConversion_sdp_bound
    {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq A1] [DecidableEq B0] [DecidableEq B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (hconvexF : Convex ℝ F.carrier) (hconvexG : Convex ℝ G.carrier)
    (N : Choi A0 A1) (Nout : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    p ≤ xiExact F N (supportValue G Nout) ∧
      ∃ W Z, exactFeasible F N (supportValue G Nout) W Z ∧
        QAlgorithms.effectProb W N = xiExact F N (supportValue G Nout) := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
