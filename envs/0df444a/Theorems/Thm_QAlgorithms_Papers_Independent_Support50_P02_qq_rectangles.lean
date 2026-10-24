-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_qq_rectangles
-- name    : QAlgorithms.Papers.Independent.Support50.P02.qq_rectangles
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:14:54.624089+00:00
-- url     : https://prove2.me/theorems/fd2c8f09-a62c-4069-82cb-91e0d2c8af2c
-- title:
--   §6: alternative qq regularized rectangles
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For independent pure states $\Psi_1^{AA'}$ and $\Psi_2^{BB'}$, let $\sigma^{ABC}=(\operatorname{id}_{AB}\otimes\mathcal N)(\Psi_1\otimes\Psi_2)$. Every information quantity in a fixed set of inequalities is evaluated on this same state. Here $I_c(U\rangle V)=H(V)-H(UV)$ and $H$ is entropy in bits.
--
--   Let $\mathcal T(\mathcal M)$ be the union of the rectangles
--   $$0\le R\le I_c(A\rangle C)_\sigma,\qquad0\le S\le I_c(B\rangle C)_\sigma.$$
--   Then
--   $$Q(\mathcal N)=\overline{\bigcup_{k\ge1}\frac1k\mathcal T(\mathcal N^{\otimes k})}.$$
--   This alternative regularized description does not identify a fixed-block rectangle union with the corresponding pentagon union.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 30, §6: alternative qq regularized rectangles

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

/-- Alternative regularized qq rectangles, PDF p.30. The source expressly says the
older characterization remains correct; no equality of individual finite-k regions. -/
theorem qq_rectangles [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop (A × B) C) (hN : IsChannel N) :
    qqMacCapacity N = closure (regularized (fun n => qqRectangles (macPower N n))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
