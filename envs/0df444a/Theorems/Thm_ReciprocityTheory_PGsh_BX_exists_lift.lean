-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_exists_lift
-- name    : ReciprocityTheory.PGsh.BX.exists_lift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:06:05.242232+00:00
-- url     : https://prove2.me/theorems/74ceaa23-edda-4b8d-bcd8-9d49f31d7287
-- title:
--   BX: exists lift
-- statement:
--   The BX construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean#L64-L72

import Definitions.Def_ReciprocityTheory_DualLattices_IsHeightUnique
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulKerZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {p : ℕ}

theorem ReciprocityTheory.PGsh.BX.exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by sorry
