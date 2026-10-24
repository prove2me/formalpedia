-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_qq_regularized
-- name    : QAlgorithms.Papers.Independent.Support50.P02.qq_regularized
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:08:06.366432+00:00
-- url     : https://prove2.me/theorems/8500089b-ef52-46dc-aceb-666dfcef2cd1
-- title:
--   Theorem 2: regularized qq capacity pentagons
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For independent pure states $\Psi_1^{AA'}$ and $\Psi_2^{BB'}$, let $\sigma^{ABC}=(\operatorname{id}_{AB}\otimes\mathcal N)(\Psi_1\otimes\Psi_2)$. Every information quantity in a fixed set of inequalities is evaluated on this same state. Here $I_c(U\rangle V)=H(V)-H(UV)$ and $H$ is entropy in bits.
--
--   Let $\mathcal P(\mathcal M)$ be the union over these inputs of the nonnegative rate pairs satisfying all three inequalities
--   $$R\le I_c(A\rangle BC)_\sigma,\qquad S\le I_c(B\rangle AC)_\sigma,\qquad R+S\le I_c(AB\rangle C)_\sigma.$$
--   Then
--   $$Q(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\mathcal P(\mathcal N^{\otimes k})}.$$
--   The product constraint applies between senders, while each sender may entangle inputs across channel uses.
--
--   **Formalization Note** The printed strict signs are corrected to non-strict signs before closure, preserving zero-rate faces.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 8, Theorem 2: regularized qq capacity pentagons

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

/-- Theorem 2, PDF p.8, proof pp.17–22: product sender inputs, all THREE
bounds on one state. Same explicit non-strict boundary correction as Theorem 1.
The p.18 one-use N tensor n notation is read as N before subsequent k-blocking. -/
theorem qq_regularized [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    qqMacCapacity N = closure (regularized (fun n => qqOne (macPower N n))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
