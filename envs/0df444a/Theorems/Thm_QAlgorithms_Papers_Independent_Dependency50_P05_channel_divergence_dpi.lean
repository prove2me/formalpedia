-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_channel_divergence_dpi
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.channel_divergence_dpi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:00:25.757454+00:00
-- url     : https://prove2.me/theorems/35cdc55a-1450-4cab-94d6-d7ae7350499c
-- title:
--   Channel-divergence data processing, pure-input reduction and invariance
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Let $D$ be one extended-real divergence family on all finite-dimensional density operators, satisfying data processing under every CPTP map. For channels $\Phi_1,\Phi_2:A_0\to A_1$ define $C_D(\Phi_1\|\Phi_2)$ as the supremum of $D((\mathrm{id}_R\otimes\Phi_1)(\rho)\|(\mathrm{id}_R\otimes\Phi_2)(\rho))$ over all positive finite reference dimensions and all density matrices $\rho$ on $RA_0$. For every superchannel $\Theta:A\to B$,
--   $$C_D(\Theta[\Phi_1]\|\Theta[\Phi_2])\le C_D(\Phi_1\|\Phi_2).$$
--   The supremum is taken in the extended reals, allowing $+\infty$. No diagonal normalization, nonnegativity, symmetry or finite-valuedness of $D$ is required. The target is the paper's local data-processing proof, rather than a new definition attributed to the paper. The supremum is unchanged when restricted to unit-vector pure inputs on A0 tensor A0, with a reference of dimension d_A0. More generally, any EReal-valued family C on all finite channel systems satisfying data processing under every superchannel is invariant under reversible unitary superchannels and obeys C(Phi tensor Lambda || Psi tensor Lambda)=C(Phi || Psi) for every fixed CPTP ancillary channel Lambda. These conclusions quantify all channel pairs and all positive finite system dimensions.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 18, Sec. V-A, Eqs.(89)–(92)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF pp.17–18, Eqs.(89)–(92) and their stated consequences:
induced-divergence data processing, restriction to pure inputs with an input-sized reference,
and reversible/tensor invariance of ANY superchannel contraction. The generic contraction
is constrained only by its data-processing property, not by these desired conclusions. -/
theorem channel_divergence_dpi (D : StateDivergence) (hD : DivergenceDPI D) :
    (∀ (A B : System) (T : Supermap A B), IsSuperchannel T →
      ∀ X Y : Mat (ChoiRegister A), ChannelChoi X → ChannelChoi Y →
        stabilizedDivergence D B (T X) (T Y) ≤ stabilizedDivergence D A X Y) ∧
    (∀ (A : System) (X Y : Mat (ChoiRegister A)), ChannelChoi X → ChannelChoi Y →
      stabilizedDivergence D A X Y =
        ⨆ v : {v : In A × In A → ℂ // ∑ i, Complex.normSq (v i) = 1},
          D (In A × Out A)
            (QAlgorithms.idTensorSuperop (action X) (ketProjector v.val))
            (QAlgorithms.idTensorSuperop (action Y) (ketProjector v.val))) ∧
    (∀ C : ChannelContraction, ChannelContractionDPI C →
      (∀ (A B : System), A.input = B.input → A.output = B.output →
        ∀ T : Supermap A B, IsReversible T →
          ∀ X Y : Mat (ChoiRegister A), ChannelChoi X → ChannelChoi Y →
            C B (T X) (T Y) = C A X Y) ∧
      (∀ (A B : System) (X Y : Mat (ChoiRegister A)) (L : Mat (ChoiRegister B)),
        ChannelChoi X → ChannelChoi Y → ChannelChoi L →
          C (productSystem A B) (productChoi X L) (productChoi Y L) = C A X Y)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
