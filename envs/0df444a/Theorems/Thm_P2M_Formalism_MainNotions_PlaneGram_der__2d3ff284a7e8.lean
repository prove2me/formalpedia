-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_der__2d3ff284a7e8
-- name    : P2M_Formalism_MainNotions_PlaneGram_der__2d3ff284a7e8
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:22.081375+00:00
-- url     : https://prove2.me/theorems/8469426b-b59e-4bdd-b26d-a2f2bc444eff
-- title:
--   P2 M Formalism Main Notions Plane Gram der  2d3ff284a7e8: P2 M Formalism Main Notions Plane Gram der  2d3ff284a7e8
-- statement:
--   The P2 M Formalism Main Notions Plane Gram der  2d3ff284a7e8 construction uses the P2 M Formalism Main Notions Plane Gram der  2d3ff284a7e8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L128-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L128-L191

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)

theorem P2M_Formalism_MainNotions_PlaneGram_der__2d3ff284a7e8 (hDER : DER K v p) (hD : DVRHyp v p) (r g : ℕ) (M : Fin r →₀ ℕ) (c : ℕ) (hc : 1 ≤ c) :
    ∃ (I : Type) (_ : Fintype I) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)),
      (∀ s, 0 ≤ v (cf s)) ∧ (∀ s, (absE (κ s) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % p ^ g) then
          monomial (ρ' s + p ^ g • (δ s + (divE (p ^ g) η - κ s))) (cf s * bin (κ s) (divE (p ^ g) η))
          else 0) := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«der'» := P2M_Formalism_MainNotions_PlaneGram_der__2d3ff284a7e8
