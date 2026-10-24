-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_cq_regularized
-- name    : QAlgorithms.Papers.Independent.Support50.P02.cq_regularized
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:07:14.419103+00:00
-- url     : https://prove2.me/theorems/69520384-f47b-4e57-868f-7fd4ebc6d09b
-- title:
--   Theorem 1: regularized cq capacity
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For a pure ensemble $\{p_x,\phi_x^{A'}\}$ and an independent pure state $\Psi^{BB'}$, let $\sigma^{XBC}=\sum_xp_x|x\rangle\langle x|\otimes(\operatorname{id}_B\otimes\mathcal N)(\phi_x\otimes\Psi)$. Write $H$ for von Neumann entropy in bits, $I(U;V)=H(U)+H(V)-H(UV)$, and $I_c(U\rangle V)=H(V)-H(UV)$.
--
--   Let $\mathcal R_{cq}(\mathcal M)$ be the union, over these inputs, of the rectangles $0\le r\le I(X;C)_\sigma$, $0\le S\le I_c(B\rangle CX)_\sigma$. The ensemble alphabet may be restricted to $|X|\le\min\{|A'|,|C|\}^2+1$, with dimensions taken for $\mathcal M$. Then
--   $$CQ(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\mathcal R_{cq}(\mathcal N^{\otimes k})}.$$
--   This gives a regularized characterization rather than a finite computation or general single-letter formula.
--
--   **Formalization Note** Non-strict inequalities correct the printed strict inequalities before closure, so zero-capacity faces are retained.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 7, Theorem 1: regularized cq capacity

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

/-- Theorem 1, PDF pp.7–8, converse p.13. Boundary correction: the printed
strict rectangle inequalities are replaced by non-strict ones before closure,
retaining zero-capacity faces. The alphabet bound is included in the characterization. -/
theorem cq_regularized [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    cqMacCapacity N = closure (regularized (fun n => cqOne (macPower N n)
      (some (min (Fintype.card (Fin n → A)) (Fintype.card (Fin n → C)) ^ 2 + 1)))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
