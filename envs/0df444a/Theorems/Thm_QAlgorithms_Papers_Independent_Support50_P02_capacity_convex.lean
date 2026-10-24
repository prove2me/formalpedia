-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_capacity_convex
-- name    : QAlgorithms.Papers.Independent.Support50.P02.capacity_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:20:44.684003+00:00
-- url     : https://prove2.me/theorems/2cc346b8-74c0-40c6-8355-e6d6cdf7ea7f
-- title:
--   §7.4: convexity of both capacity regions
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For either $\mathcal K=CQ(\mathcal N)$ or $\mathcal K=Q(\mathcal N)$, any $u,v\in\mathcal K$ and any $\lambda\in[0,1]$ satisfy
--   $$\lambda u+(1-\lambda)v\in\mathcal K.$$
--   Thus both full operational capacity regions are convex. No extra convex-hull operation is added to the regularized capacity descriptions.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 8, §7.4: convexity of both capacity regions

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

/-- Convexity of BOTH full operational capacity regions, §7.4, PDF p.35,
announced p.8. Convexification is not inserted into any capacity formula. -/
theorem capacity_convex [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    Convex ℝ (cqMacCapacity N) ∧ Convex ℝ (qqMacCapacity N) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
