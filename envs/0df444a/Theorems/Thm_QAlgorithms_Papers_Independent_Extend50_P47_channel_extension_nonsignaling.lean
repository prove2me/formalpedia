-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_channel_extension_nonsignaling
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.channel_extension_nonsignaling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:39:16.921164+00:00
-- url     : https://prove2.me/theorems/0d2c2a52-43a7-4518-992b-0fc2e8999c4d
-- title:
--   Channel extension implies no signaling, (233)–(238)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   For CPTP M extending N in the sense TrR′∘M=N∘TrR, one has TrR′∘M=TrR′∘M∘(replacement on R by IR/dim R, identity on S).
--
--   $$
--   \operatorname{Tr}_{R'}\mathcal M(X)=\operatorname{Tr}_{R'}\mathcal M\!\left(\frac{I_R}{\dim R}\otimes\operatorname{Tr}_R X\right)\qquad(\forall X).
--   $$
--
--   Both maps are CPTP and $\operatorname{Tr}_{R'}\mathcal M=\mathcal N\operatorname{Tr}_R$ on every operator. Only $R$ is replaced by its normalized identity.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 35, Channel extension implies no signaling, (233)–(238)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.su2BorelSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P47.u2BorelSpace

/-- PDF pp.35–36, (233)–(238): replace R alone, retaining every S block.
The equality holds on all operators, including those of entangled inputs. -/
theorem channel_extension_nonsignaling [Nonempty S] [Nonempty R] [Nonempty R2] [Nonempty S2] (N : Superop S S2) (hN : IsChannel N)
    (M : Superop (R × S) (R2 × S2)) (hM : ChannelExtension N M) :
    ∀ X : Mat (R × S), traceLeft (M X) = traceLeft (M (replaceReference X)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
