-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_card_fibre_cons
-- name    : ReciprocityTheory.PGsh.card_fibre_cons
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:08.821715+00:00
-- url     : https://prove2.me/theorems/29ae27d9-42a6-53b5-a478-300b1e917b45
-- title:
--   PGsh: card fibre cons
-- statement:
--   The PGsh construction uses the card fibre cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L373-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L373-L377

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}

theorem ReciprocityTheory.PGsh.card_fibre_cons {s m : ℕ} (k₀ : Fin s) (φ : Fin m → Fin s) (k : Fin s) :
    #{a | (Fin.cons k₀ φ : Fin (m + 1) → Fin s) a = k} = #{a | φ a = k} + if k₀ = k then 1 else 0 := by sorry
