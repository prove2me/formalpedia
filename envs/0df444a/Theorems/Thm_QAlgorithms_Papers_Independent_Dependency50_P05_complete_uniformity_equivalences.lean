-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_complete_uniformity_equivalences
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.complete_uniformity_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:54:36.475978+00:00
-- url     : https://prove2.me/theorems/5afe901e-a447-43c6-95de-2bf1c38280f5
-- title:
--   Complete uniformity preservation and strict inclusion
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Assume the input dimensions and output dimensions match separately. For a superchannel $\Theta$, the following are equivalent:
--
--   1. For every auxiliary dynamical system $C$, $\Theta\otimes1^C$ preserves channels whose $A_1$ output is uniform and independent of the remaining registers.
--   2. Its Choi matrix satisfies positivity and Eq.(19), and
--   $$J^{A_0B}=J^{A_0B_0}\otimes u^{B_1}.$$
--   3. It has a pre/post CPTP realization with $1\le d_E\le d_{A_0}d_{B_0}$ for which $\Gamma_{\rm post}(u^{A_1}\otimes R)=\operatorname{Tr}(R)u^{B_1}$ for every operator $R$ on $E$.
--
--   There also exist some isomorphic input/output system pairs admitting a completely uniformity preserving superchannel whose dual is not a superchannel. The strictness assertion is existential over dimensions; it does not assert strictness in every dimension. This separates the two noise models.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 10, Theorem 3, Eqs.(55)–(56)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.9–11, Theorem 3. The final existential records that the
converse to doubly-stochastic implies complete uniformity fails in SOME dimensions. -/
theorem complete_uniformity_equivalences {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsSuperchannel T) :
    (CompletelyUniformityPreserving T ↔ StandardMarginals T ∧ UniformFactorization T) ∧
    (CompletelyUniformityPreserving T ↔ ∃ e : ℕ, 0 < e ∧ e ≤ A.input * B.input ∧
      ∃ (P : Mat (In B × (In A × Fin e))) (Q : Mat ((Out A × Fin e) × Out B)),
        ChannelChoi P ∧ ChannelChoi Q ∧ Realizes T e P Q ∧
        DepolarizingPost (A := A) (B := B) e Q) ∧
    (∃ (C D : System) (S : Supermap C D), C.input = D.input ∧ C.output = D.output ∧
      IsSuperchannel S ∧ CompletelyUniformityPreserving S ∧ ¬ IsDoublyStochastic S) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
