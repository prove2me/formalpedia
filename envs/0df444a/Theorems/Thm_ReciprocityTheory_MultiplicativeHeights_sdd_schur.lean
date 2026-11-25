-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_schur
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_schur
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:23.239196+00:00
-- url     : https://prove2.me/theorems/7bddc3f5-68a1-4c38-9f8e-6f267505c4b5
-- title:
--   Multiplicative Heights: sdd schur
-- statement:
--   The Multiplicative Heights construction uses the sdd schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L193-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L193-L212

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_schur {r k₀ k₁ : ℕ} (B : Matrix (Fin r) (Fin k₀) ℂ) (C : Matrix (Fin r) (Fin k₁) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : Hᴴ = H) (hG : (Bᴴ * H * B).IsHermitian)
    (hu : IsUnit (Bᴴ * H * B).det) :
    Cᴴ * H * C - (Cᴴ * H * B) * (Bᴴ * H * B)⁻¹ * (Bᴴ * H * C) =
      (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C)))ᴴ * H *
        (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C))) := by sorry
