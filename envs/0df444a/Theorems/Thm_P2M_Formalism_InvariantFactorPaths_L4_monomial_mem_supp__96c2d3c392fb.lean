-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_monomial_mem_supp__96c2d3c392fb
-- name    : P2M_Formalism_InvariantFactorPaths_L4_monomial_mem_supp__96c2d3c392fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:39.735054+00:00
-- url     : https://prove2.me/theorems/561d954e-2f8a-44e6-ae14-f1b482000675
-- title:
--   P2 M Formalism Invariant Factor Paths L4 monomial mem supp  96c2d3c392fb: P2 M Formalism Invariant Factor Paths L4 monomial mem supp  96c2d3c392fb
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 monomial mem supp  96c2d3c392fb construction uses the P2 M Formalism Invariant Factor Paths L4 monomial mem supp  96c2d3c392fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L117-L123

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

theorem P2M_Formalism_InvariantFactorPaths_L4_monomial_mem_supp__96c2d3c392fb {σ : Type} (Q : Set (σ →₀ ℕ)) (m : σ →₀ ℕ) (hm : m ∈ Q) :
    monomial m (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] Q := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«monomial_mem_supp'» := P2M_Formalism_InvariantFactorPaths_L4_monomial_mem_supp__96c2d3c392fb
