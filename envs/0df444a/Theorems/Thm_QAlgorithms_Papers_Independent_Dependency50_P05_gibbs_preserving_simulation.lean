-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_gibbs_preserving_simulation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.gibbs_preserving_simulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:04:11.387077+00:00
-- url     : https://prove2.me/theorems/8cc65f87-1e32-4e31-97ae-40776b7519ed
-- title:
--   Simulation by Gibbs-replacer-preserving superchannels
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Psi^A,\Phi^B$ be channels and let $\gamma_A^{A_1},\gamma_B^{B_1}$ be supplied density matrices representing their Gibbs states. Define the free replacers $\Pi_A(X)=\operatorname{Tr}(X)\gamma_A$ and $\Pi_B(X)=\operatorname{Tr}(X)\gamma_B$. A superchannel sending $\Psi$ to $\Phi$ and $\Pi_A$ to $\Pi_B$ exists if and only if, for every pair of test channels $\Lambda_1,\Lambda_2$ on a copy $R$ of $B$,
--   $$H_{\min}^{\rm ext}(R|A)_{(\Psi\otimes\Lambda_1+\Pi_A\otimes\Lambda_2)/2}\le H_{\min}^{\rm ext}(R|B)_{(\Phi\otimes\Lambda_1+\Pi_B\otimes\Lambda_2)/2}.$$
--   This specializes the simultaneous comparison criterion to the two required transformations. Gibbs preservation here means preservation of the Gibbs replacer; covariance, thermal operations and energy-preserving realizations are not hypotheses or conclusions.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 21, Sec. V-E

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.21, Sec.V-E: Gibbs-REPLACER preservation only.
The criterion is Corollary 1 with the ordinary channel and its Gibbs replacer as the two tests. -/
theorem gibbs_preserving_simulation (A B : System) (X : Mat (ChoiRegister A)) (Y : Mat (ChoiRegister B))
    (hX : ChannelChoi X) (hY : ChannelChoi Y)
    (GA : Mat (Out A)) (GB : Mat (Out B)) (hGA : QAlgorithms.IsDensityMatrix GA) (hGB : QAlgorithms.IsDensityMatrix GB) :
    (∃ T : Supermap A B, IsSuperchannel T ∧ T X = Y ∧ T (gibbsChoi A GA) = gibbsChoi B GB) ↔
    ∀ K L : Mat (ChoiRegister B), ChannelChoi K → ChannelChoi L →
      entropyContraction A B K L X (gibbsChoi A GA) ≤
        entropyContraction B B K L Y (gibbsChoi B GB) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
