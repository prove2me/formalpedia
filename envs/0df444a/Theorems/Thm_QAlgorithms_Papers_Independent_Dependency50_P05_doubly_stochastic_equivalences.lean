-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_doubly_stochastic_equivalences
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.doubly_stochastic_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:53:06.05498+00:00
-- url     : https://prove2.me/theorems/ae7729ed-7b48-45a1-ba9f-de3ded70450c
-- title:
--   Three characterizations of double stochasticity
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Theta:A\to B$ be a superchannel and suppose $d_{A_0}d_{B_1}=d_{B_0}d_{A_1}$. The following are equivalent:
--
--   1. Its Hilbert–Schmidt dual is a superchannel.
--   2. $J_\Theta\ge0$, $J^{A_1B_0}=I$, $J^{AB_0}=J^{A_0B_0}\otimes u^{A_1}$, and
--   $$J^{A_0B_1}=I,\qquad J^{A_0B}=J^{A_0B_0}\otimes u^{B_1}.$$
--   3. There exist a memory $E$ with $1\le d_E\le d_{A_0}d_{B_0}$ and CPTP maps $\Gamma_{\rm pre}:B_0\to A_0E$, $\Gamma_{\rm post}:A_1E\to B_1$ realizing $\Theta[\Phi]=\Gamma_{\rm post}\circ(\Phi\otimes\mathrm{id}_E)\circ\Gamma_{\rm pre}$ on every linear map, such that for every operator $R$ on $E$,
--   $$\Gamma_{\rm post}(u^{A_1}\otimes R)=\operatorname{Tr}(R)u^{B_1},\qquad \operatorname{Tr}_E\Gamma_{\rm pre}(u^{B_0})=u^{A_0}.$$
--   These conditions describe an existential realization, with the memory bound supplied by Theorem 1.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 8, Theorem 2, Eqs.(48)–(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.8–9, Theorem 2, Eqs.(48)–(50). The memory and BOTH channels
are existential, with the Theorem 1 memory bound; identities are not imposed on arbitrary dilations. -/
theorem doubly_stochastic_equivalences {A B : System}
    (hd : A.input * B.output = B.input * A.output) (T : Supermap A B)
    (hT : IsSuperchannel T) :
    (IsDoublyStochastic T ↔
      StandardMarginals T ∧ jA0B1 T = 1 ∧ UniformFactorization T) ∧
    (IsDoublyStochastic T ↔ ∃ e : ℕ, 0 < e ∧ e ≤ A.input * B.input ∧
      ∃ (P : Mat (In B × (In A × Fin e))) (Q : Mat ((Out A × Fin e) × Out B)),
        ChannelChoi P ∧ ChannelChoi Q ∧ Realizes T e P Q ∧
        DepolarizingPost (A := A) (B := B) e Q ∧ UniformPre (A := A) (B := B) e P) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
