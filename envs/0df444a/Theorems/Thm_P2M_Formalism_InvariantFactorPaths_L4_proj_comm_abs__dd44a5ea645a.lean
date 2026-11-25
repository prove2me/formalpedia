-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_proj_comm_abs__dd44a5ea645a
-- name    : P2M_Formalism_InvariantFactorPaths_L4_proj_comm_abs__dd44a5ea645a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:53.796725+00:00
-- url     : https://prove2.me/theorems/c6968734-721b-4f88-932a-8edff9c94e01
-- title:
--   P2 M Formalism Invariant Factor Paths L4 proj comm abs  dd44a5ea645a: P2 M Formalism Invariant Factor Paths L4 proj comm abs  dd44a5ea645a
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 proj comm abs  dd44a5ea645a construction uses the P2 M Formalism Invariant Factor Paths L4 proj comm abs  dd44a5ea645a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L11-L33

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem P2M_Formalism_InvariantFactorPaths_L4_proj_comm_abs__dd44a5ea645a (PE A : V →ₗ[k] V) (R W L : Submodule k V) (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = R ⊓ W) (h3 : LinearMap.ker PE ⊓ W = L ⊓ W)
    (hR : ∀ x ∈ R, A x ∈ R) (hW : ∀ x ∈ W, A x ∈ W) (hL : ∀ x ∈ L, A x ∈ L) :
    ∀ x ∈ W, PE (A x) = A (PE x) := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«proj_comm_abs'» := P2M_Formalism_InvariantFactorPaths_L4_proj_comm_abs__dd44a5ea645a
