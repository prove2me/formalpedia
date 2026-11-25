-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_constantCoeff_specRest_439e19de31d5
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_constantCoeff_specRest_439e19de31d5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:02.763791+00:00
-- url     : https://prove2.me/theorems/e5a156fc-ab6d-4cb4-8546-926e936727f8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible constant Coeff spec Rest 439e19de31d5: P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible constant Coeff spec Rest 439e
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible constant Coeff spec Rest 439e19de31d5 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible constant Coeff spec Rest 439e19de31d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L27-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L27-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_constantCoeff_specRest_439e19de31d5 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {δ : ℕ}
    (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) R} (hf : IsMultiHomog δ f)
    (y : Par e n → S) : constantCoeff (specRest φ f y) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenChowIrreducible».«constantCoeff_specRest» := P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_constantCoeff_specRest_439e19de31d5
