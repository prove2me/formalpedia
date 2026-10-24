-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_qq_scenarios
-- name    : QAlgorithms.Papers.Independent.Support50.P02.qq_scenarios
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:13:44.554726+00:00
-- url     : https://prove2.me/theorems/62d7e007-0dc5-4866-9586-5ec87ff19271
-- title:
--   §5: qq scenario equivalence
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   Let $Q_I,Q_{II},Q_{III}$ denote the closed qq rate regions for entanglement generation, entanglement transmission, and strong subspace transmission. Generation starts from independent pure reference/input preparations. Transmission applies separate local CPTP encoders to halves of independent Bell states. Strong transmission must preserve every pair of independent pure reference/input states, with arbitrary finite reference dimensions. In every case success uses one joint fidelity to the product target. Then
--   $$Q_I(\mathcal N)=Q_{II}(\mathcal N)=Q_{III}(\mathcal N).$$
--   This permits the same closed region to describe all three tasks, without adding free shared randomness.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 7, §5: qq scenario equivalence

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

/-- QQ scenario equivalence, PDF p.7 and §§5.2–5.4, pp.24–29.
Arbitrary references stay independent across senders; equality concerns CLOSED regions. -/
theorem qq_scenarios [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    qqMacCapacity N .generation = qqMacCapacity N .transmission ∧
    qqMacCapacity N .transmission = qqMacCapacity N .strong := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
