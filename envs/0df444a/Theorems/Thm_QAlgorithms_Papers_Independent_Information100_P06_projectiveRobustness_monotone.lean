-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_projectiveRobustness_monotone
-- name    : QAlgorithms.Papers.Independent.Information100.P06.projectiveRobustness_monotone
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:28:39.569987+00:00
-- url     : https://prove2.me/theorems/c6bafc3a-5572-44bb-8595-03bbc387ecd0
-- title:
--   Theorem 12: dynamical projective-robustness monotonicity
-- statement:
--   Let A and B be finite-dimensional complex dynamical systems with positive input and output dimensions. Represent each CPTP channel N by its normalized Choi matrix J_N, with the input index first. Let F_A and F_B be nonempty sets of free CPTP channels. A successful physical superinstrument branch is completely CP preserving and completely CPTNI preserving, belongs to a two-outcome superinstrument whose sum is completely CPTP preserving, and sends every free channel into the nonnegative cone of free channels, including the zero branch. Suppose its action on N is p N', where p>0 is independent of the transmitted state and N' is CPTP.
--
--   Define the dynamical projective robustness by
--   $$
--   \Omega_{F_A}(N)=\inf\{\gamma\ge0:\exists\lambda\ge0,\ M\in F_A,\ J_N\preceq\lambda J_M\preceq\gamma J_N\},
--   $$
--   with value +infinity if no sandwich exists. Then
--   $$
--   \Omega_{F_B}(N')\le\Omega_{F_A}(N).
--   $$
--   This is the dynamical monotonicity obstruction for exact probabilistic free conversion.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 14, Theorem 12: dynamical projective-robustness monotonicity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF p.14, Theorem 12: dynamical projective robustness cannot increase
under a physical probabilistic RNG transformation. The successful scalar is
strictly positive and multiplies a complete normalized channel. -/
theorem projectiveRobustness_monotone
    {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (N : Choi A0 A1) (Nout : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    projectiveRobustness G Nout ≤ projectiveRobustness F N := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
