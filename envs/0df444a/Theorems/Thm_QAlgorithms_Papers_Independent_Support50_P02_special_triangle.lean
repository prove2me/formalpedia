-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_special_triangle
-- name    : QAlgorithms.Papers.Independent.Support50.P02.special_triangle
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:09:55.283906+00:00
-- url     : https://prove2.me/theorems/a61c7389-2bf0-4aba-b67c-bafe775cd905
-- title:
--   Unnumbered corollary: special triangle inequality
-- statement:
--   Let $\phi$ be a unit vector and let $\rho,\sigma$ be density operators on the same finite, positive-dimensional complex Hilbert space. Write $F$ for squared Uhlmann fidelity and $\|\cdot\|_1$ for the full trace norm. Then
--   $$F(\phi,\sigma)\ge F(\phi,\rho)-\|\rho-\sigma\|_1.$$
--   The pure target is essential to this corollary's linear dependence on the other state.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 10, Unnumbered corollary: special triangle inequality

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

/-- Corollary to Lemma 1, PDF p.10: the special triangle inequality has a PURE target. -/
theorem special_triangle [Nonempty A] (phi : EuclideanSpace ℂ A) (hp : IsState phi)
    (rho sigma : Op A) (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) :
    squaredFidelity (pureDensity phi) rho - traceNorm (rho - sigma) ≤
      squaredFidelity (pureDensity phi) sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
