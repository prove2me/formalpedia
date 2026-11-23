-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_cartan_comm_erase__7d4a3ad236fe
-- name    : P2M_Formalism_InvariantFactorPaths_L4_cartan_comm_erase__7d4a3ad236fe
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:37.327226+00:00
-- url     : https://prove2.me/theorems/b6b58032-8973-4307-9403-7e6bf3ac1eef
-- title:
--   P2 M Formalism Invariant Factor Paths L4 cartan comm erase  7d4a3ad236fe: P2 M Formalism Invariant Factor Paths L4 cartan comm erase  7d4a3ad236fe
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 cartan comm erase  7d4a3ad236fe construction uses the P2 M Formalism Invariant Factor Paths L4 cartan comm erase  7d4a3ad236fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L125-L132

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem P2M_Formalism_InvariantFactorPaths_L4_cartan_comm_erase__7d4a3ad236fe (LL : Letters N) (j : ℕ) (ρ : Fin r) (a : Fin r) (ha : a ∈ univ.erase ρ) (b : Fin r)
    (hb : b ∈ univ.erase ρ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j ρ ρ (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j ρ ρ x) := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«cartan_comm_erase'» := P2M_Formalism_InvariantFactorPaths_L4_cartan_comm_erase__7d4a3ad236fe
