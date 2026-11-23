-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_fock_monomial_zero__a5d7011b8429
-- name    : P2M_Formalism_InvariantFactorPaths_L4_fock_monomial_zero__a5d7011b8429
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:25.450346+00:00
-- url     : https://prove2.me/theorems/7f632b39-a81a-4867-bf68-ef8569f25f05
-- title:
--   P2 M Formalism Invariant Factor Paths L4 fock monomial zero  a5d7011b8429: P2 M Formalism Invariant Factor Paths L4 fock monomial zero  a5d7011b8429
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 fock monomial zero  a5d7011b8429 construction uses the P2 M Formalism Invariant Factor Paths L4 fock monomial zero  a5d7011b8429 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L105-L111

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

theorem P2M_Formalism_InvariantFactorPaths_L4_fock_monomial_zero__a5d7011b8429 {σ : Type} (g : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (hm : m ∉ g.support) :
    fock p g (monomial m 1) = 0 := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«fock_monomial_zero'» := P2M_Formalism_InvariantFactorPaths_L4_fock_monomial_zero__a5d7011b8429
