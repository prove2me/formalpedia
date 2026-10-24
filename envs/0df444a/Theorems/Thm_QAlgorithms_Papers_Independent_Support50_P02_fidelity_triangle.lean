-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_fidelity_triangle
-- name    : QAlgorithms.Papers.Independent.Support50.P02.fidelity_triangle
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:12:05.950417+00:00
-- url     : https://prove2.me/theorems/52c3f6eb-9068-43f6-ab4d-222c158c0ec2
-- title:
--   Unnumbered derived fidelity bound (16)
-- statement:
--   Let $\rho_1,\rho_2,\rho_3$ be density operators on the same finite, positive-dimensional complex Hilbert space, and let $F$ denote squared Uhlmann fidelity. Then
--   $$F(\rho_1,\rho_3)\ge1-2\sqrt{1-F(\rho_1,\rho_2)}-2\sqrt{1-F(\rho_2,\rho_3)}.$$
--   This is the paper's derived triangle-type estimate; neither coefficient $2$ is strengthened or removed.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 10, Unnumbered derived fidelity bound (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Equation (16), PDF p.10: the derived fidelity triangle bound, both constants TWO. -/
theorem fidelity_triangle [Nonempty A] (rho1 rho2 rho3 : Op A)
    (h1 : IsDensityMatrix rho1) (h2 : IsDensityMatrix rho2) (h3 : IsDensityMatrix rho3) :
    1 - 2 * Real.sqrt (1 - squaredFidelity rho1 rho2) -
      2 * Real.sqrt (1 - squaredFidelity rho2 rho3) ≤ squaredFidelity rho1 rho3 := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
