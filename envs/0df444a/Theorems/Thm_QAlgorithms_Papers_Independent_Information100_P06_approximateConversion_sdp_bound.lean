-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_approximateConversion_sdp_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P06.approximateConversion_sdp_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:31:19.337361+00:00
-- url     : https://prove2.me/theorems/560bee1a-19e7-4dad-9bd6-439b6e32949e
-- title:
--   Proposition 16: SDP bound for approximate pure-target conversion
-- statement:
--   Let A and B be finite-dimensional complex dynamical systems with positive input and output dimensions. Represent each CPTP channel N by its normalized Choi matrix J_N, with the input index first. Let F_A and F_B be nonempty sets of free CPTP channels. A successful physical superinstrument branch is completely CP preserving and completely CPTNI preserving, belongs to a two-outcome superinstrument whose sum is completely CPTP preserving, and sends every free channel into the nonnegative cone of free channels, including the zero branch. Suppose its action on N is p N', where p>0 is independent of the transmitted state and N' is CPTP.
--
--   Assume F_A and F_B are convex. Let Phi be a CPTP channel whose normalized Choi state is pure. Fix a requested fidelity f in [0,1] and suppose Tr(J_Phi J_N')>=f. Put v=sup_{M in F_B} Tr(Pi_{J_Phi} J_M); since the target is pure, Pi_{J_Phi}=J_Phi. Define Xi_f as the maximum of Tr(Z J_N), subject to
--   $$
--   0\preceq W\preceq Z\preceq d\,\sigma\otimes I_{A_1},\quad \sigma\text{ a density matrix},\quad d=\dim A_0,
--   $$
--   $$
--   \operatorname{Tr}(WJ_N)=f\operatorname{Tr}(ZJ_N),\qquad
--   \operatorname{Tr}(WJ_M)\le v\operatorname{Tr}(ZJ_M)\quad\forall M\in F_A.
--   $$
--   Then p<=Xi_f and the maximum is attained. The equality uses the requested threshold even when the achieved fidelity is larger. This states the approximate pure-target conversion ceiling.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 15, Proposition 16: SDP bound for approximate pure-target conversion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF pp.15–16, Proposition 16: SDP ceiling for approximate conversion to
a pure normalized Choi target. The requested fidelity is in [0,1]; the output
may exceed it, while the SDP retains the source's equality constraint.
Printed Eq.99 labels Xi with V_FC(Nout); Eqs.100–102 instead use the
requested threshold and V_FC(Phi). The formal optimization uses those
constraint parameters because its feasible set has no other Nout dependence. -/
theorem approximateConversion_sdp_bound
    {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq A1] [DecidableEq B0] [DecidableEq B1]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (hconvexF : Convex ℝ F.carrier) (hconvexG : Convex ℝ G.carrier)
    (N : Choi A0 A1) (Nout Phi : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (hPhi : IsChannelChoi Phi) (hpure : Phi * Phi = Phi)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hfidelity : f ≤ QAlgorithms.effectProb Phi Nout)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    p ≤ xiApproximate F N f (supportValue G Phi) ∧
      ∃ W Z, approximateFeasible F N f (supportValue G Phi) W Z ∧
        QAlgorithms.effectProb Z N = xiApproximate F N f (supportValue G Phi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
