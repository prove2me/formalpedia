-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_degradable_sum_additive
-- name    : QAlgorithms.Papers.Independent.Support50.P02.degradable_sum_additive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:15:54.460662+00:00
-- url     : https://prove2.me/theorems/b6dc2498-8cc5-48bd-bb46-522b317081ae
-- title:
--   §6: optimized qq sum-information additivity
-- statement:
--   Let $\mathcal N:A'B'\to C$ be a completely positive, trace-preserving channel between finite, positive-dimensional complex quantum registers. Alice and Bob control separate inputs. Codes use independent sender preparations, local encoders, one joint memoryless channel and one joint decoder, with external references untouched and no free shared resources. Fidelity is squared Uhlmann fidelity, trace distance is the full trace norm, and entropies are in bits. Write $CQ(\mathcal N)$ and $Q(\mathcal N)$ for the closed operational classical–quantum and quantum–quantum capacity regions, using joint output fidelity and nonnegative rates.
--
--   For independent pure states $\Psi_1^{AA'}$ and $\Psi_2^{BB'}$, let $\sigma^{ABC}=(\operatorname{id}_{AB}\otimes\mathcal N)(\Psi_1\otimes\Psi_2)$. Every information quantity in a fixed set of inequalities is evaluated on this same state. Here $I_c(U\rangle V)=H(V)-H(UV)$ and $H$ is entropy in bits.
--
--   Suppose $\mathcal N$ is degradable: for an isometric extension $U:A'B'\to CE$ there is a CPTP map $\mathcal D:C\to E$ with $\mathcal N^c=\mathcal D\circ\mathcal N$, using the complement of that same extension. Define $J(\mathcal M)=\max_{\Psi_1\otimes\Psi_2}I_c(AB\rangle C)_\sigma$. For every positive integer $k$,
--   $$J(\mathcal N^{\otimes k})=kJ(\mathcal N).$$
--   The optimization retains product inputs between senders and allows correlations across uses within either sender. This concerns the optimized information sum, not single-letterization of the full region.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 30, §6: optimized qq sum-information additivity

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

/-- Optimized qq sum-information additivity, PDF p.30, repeated uses of ONE
channel. Degradability uses the receiver and complement of the SAME dilation;
no joint entangled sender input or signed capacity conclusion is asserted. -/
theorem degradable_sum_additive [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E]
    (U : Matrix (C × E) (A × B) ℂ) (hU : IsDegradable U) (n : ℕ) (hn : 0 < n) :
    optimizedSum (macPower (receiverChannel U) n) = (n : ℝ) * optimizedSum (receiverChannel U) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
