-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_complete_two_channel_contractions
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.complete_two_channel_contractions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:02:38.405529+00:00
-- url     : https://prove2.me/theorems/eb4265ca-0ed5-49e5-890e-1f8ecd7239e4
-- title:
--   Complete increasing family of two-channel contractions
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $\Psi_1,\Psi_2$ be channels on $A$ and $\Phi_1,\Phi_2$ channels on $B$. For every pair of test channels $\Lambda_1,\Lambda_2$ on a copy $R$ of $B$, define
--   $$C_\Lambda(\Psi_1\|\Psi_2)=H_{\min}^{\rm ext}(R|A)_{(\Psi_1\otimes\Lambda_1+\Psi_2\otimes\Lambda_2)/2}.$$
--   There exists one superchannel sending $\Psi_1$ to $\Phi_1$ and $\Psi_2$ to $\Phi_2$ if and only if $C_\Lambda(\Psi_1\|\Psi_2)\le C_\Lambda(\Phi_1\|\Phi_2)$ for every pair of test channels. This is the increasing entropy direction used in Remark 6. No metric axioms are claimed.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 20, Remark 6

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.20, Remark 6: complete increasing family of contractions.
No symmetry, positivity, or vanishing-on-equal-input property is asserted. -/
theorem complete_two_channel_contractions (A B : System)
    (X Y : Mat (ChoiRegister A)) (P Q : Mat (ChoiRegister B))
    (hX : ChannelChoi X) (hY : ChannelChoi Y) (hP : ChannelChoi P) (hQ : ChannelChoi Q) :
    (∃ T : Supermap A B, IsSuperchannel T ∧ T X = P ∧ T Y = Q) ↔
    ∀ K L : Mat (ChoiRegister B), ChannelChoi K → ChannelChoi L →
      entropyContraction A B K L X Y ≤ entropyContraction B B K L P Q := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
