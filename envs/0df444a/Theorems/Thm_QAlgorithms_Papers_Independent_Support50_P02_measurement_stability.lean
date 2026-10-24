-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_measurement_stability
-- name    : QAlgorithms.Papers.Independent.Support50.P02.measurement_stability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:09:05.189983+00:00
-- url     : https://prove2.me/theorems/26be64eb-1819-4af8-9e62-05c235bd9b72
-- title:
--   Lemma 1: measurement stability
-- statement:
--   Let $\rho$ and $\sigma$ be density operators on the same finite, positive-dimensional complex Hilbert space. Let $\Lambda$ be any effect, meaning $0\preceq\Lambda\preceq I$. With $\|\cdot\|_1$ the full trace norm,
--   $$\operatorname{Tr}(\Lambda\sigma)\ge\operatorname{Tr}(\Lambda\rho)-\|\rho-\sigma\|_1.$$
--   This controls the loss in the success probability of any effect when its input state changes. The coefficient is exactly the printed coefficient $1$.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 10, Lemma 1: measurement stability

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

/-- Lemma 1, PDF p.10: any effect, with the printed coefficient ONE and full trace norm. -/
theorem measurement_stability [Nonempty A] (rho sigma L : Op A)
    (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma) (hL : IsEffect L) :
    effectProb L rho - traceNorm (rho - sigma) ≤ effectProb L sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
