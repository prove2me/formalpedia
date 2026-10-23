-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P06_projectiveRobustness_submultiplicative
-- name    : QAlgorithms.Papers.Independent.Information100.P06.projectiveRobustness_submultiplicative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:30:07.797998+00:00
-- url     : https://prove2.me/theorems/81015b22-d380-421e-bd59-009ab3a0d6b1
-- title:
--   Proposition 14: submultiplicativity of dynamical projective robustness
-- statement:
--   Let N_1 and N_2 be CPTP channels on finite complex systems with positive input and output dimensions. Let F_1, F_2, and F_12 be nonempty sets of free CPTP channels for their individual and joint systems. Assume tensor closure: M_1 tensor M_2 belongs to F_12 whenever M_i belongs to F_i. With projective robustness defined by the normalized Choi CP sandwich and an empty feasible infimum equal to +infinity,
--   $$
--   \Omega_{F_{12}}(N_1\otimes N_2)\le\Omega_{F_1}(N_1)\Omega_{F_2}(N_2).
--   $$
--   The product is taken in the extended nonnegative reals. This is the submultiplicative bound used for multichannel distillation.
-- source:
--   Universal Improvement of Channel Fidelity via Entanglement Assistance, arXiv:2610.05669v1, PDF p. 14, Proposition 14: submultiplicativity of dynamical projective robustness

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Information100.P06

/-- PDF pp.14–15, Proposition 14: submultiplicativity in the extended
nonnegative reals, assuming exactly the tensor closure used in the proof. -/
theorem projectiveRobustness_submultiplicative
    {I1 O1 I2 O2 : Type}
    [Fintype I1] [Fintype O1] [Fintype I2] [Fintype O2]
    [DecidableEq I1] [DecidableEq I2]
    [Nonempty I1] [Nonempty O1] [Nonempty I2] [Nonempty O2]
    (F : FreeSet I1 O1) (G : FreeSet I2 O2)
    (H : FreeSet (I1 × I2) (O1 × O2))
    (htensor : ∀ M ∈ F.carrier, ∀ L ∈ G.carrier, tensorChoi M L ∈ H.carrier)
    (N : Choi I1 O1) (L : Choi I2 O2)
    (hN : IsChannelChoi N) (hL : IsChannelChoi L) :
    projectiveRobustness H (tensorChoi N L) ≤
      projectiveRobustness F N * projectiveRobustness G L := by sorry

end QAlgorithms.Papers.Independent.Information100.P06

end
