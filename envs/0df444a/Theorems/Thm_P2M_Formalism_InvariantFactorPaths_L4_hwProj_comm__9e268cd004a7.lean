-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_hwProj_comm__9e268cd004a7
-- name    : P2M_Formalism_InvariantFactorPaths_L4_hwProj_comm__9e268cd004a7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:57.904337+00:00
-- url     : https://prove2.me/theorems/a28c22c0-8ed3-4428-92b6-522ad1dc91b4
-- title:
--   P2 M Formalism Invariant Factor Paths L4 hw Proj comm  9e268cd004a7: P2 M Formalism Invariant Factor Paths L4 hw Proj comm  9e268cd004a7
-- statement:
--   The P2 M Formalism Invariant Factor Paths L4 hw Proj comm  9e268cd004a7 construction uses the P2 M Formalism Invariant Factor Paths L4 hw Proj comm  9e268cd004a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L59-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjection.lean#L59-L91

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

theorem P2M_Formalism_InvariantFactorPaths_L4_hwProj_comm__9e268cd004a7 (LL : Letters N) (j : ℕ) (ρ : Fin r) (la : Fin r → ℤ)
    (PE A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la)
    (h3 : LinearMap.ker PE ⊓ WtSpC p LL j univ la = lowIm' p LL j ρ ⊓ WtSpC p LL j univ la)
    (hA : ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x, A (glAct p LL j c d x) = glAct p LL j c d (A x))
    (hW : ∀ x ∈ WtSpC p LL j univ la, A x ∈ WtSpC p LL j univ la) :
    ∀ x ∈ WtSpC p LL j univ la, PE (A x) = A (PE x) := by sorry

alias «Formalism».«InvariantFactorPaths».«L4».«hwProj_comm'» := P2M_Formalism_InvariantFactorPaths_L4_hwProj_comm__9e268cd004a7
