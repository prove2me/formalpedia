-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_card_lift_unimod__01843a216c6e
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_card_lift_unimod__01843a216c6e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:51.969571+00:00
-- url     : https://prove2.me/theorems/922aed3f-8c4c-4c5a-b2e5-a70971c3bd52
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 First Proposition Frame card lift unimod  01843a216c6e: P2 M Formalism Hermitian Lattices Ext L3 First Proposition Frame card lift unimod  01843a216c6e
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 First Proposition Frame card lift unimod  01843a216c6e construction uses the P2 M Formalism Hermitian Lattices Ext L3 First Proposition Frame card lift unimod  01843a216c6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftUnimod.lean#L86-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftUnimod.lean#L86-L117

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem P2M_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_card_lift_unimod__01843a216c6e [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a))
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {θ e : A}
    (he : (θ - star θ) * e = 1) (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) (q : ℕ)
    (hq : Nat.card (RingHom.ker π) = q ^ 2) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} =
      q ^ (Fintype.card m ^ 2) * Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«FirstPropositionFrame».«card_lift_unimod'» := P2M_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_card_lift_unimod__01843a216c6e
