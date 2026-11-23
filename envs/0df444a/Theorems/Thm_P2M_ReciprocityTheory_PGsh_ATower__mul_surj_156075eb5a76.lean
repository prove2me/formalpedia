-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_ATower__mul_surj_156075eb5a76
-- name    : P2M_ReciprocityTheory_PGsh_ATower__mul_surj_156075eb5a76
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:04.432521+00:00
-- url     : https://prove2.me/theorems/0c3af81d-b59a-43c4-a961-ed266c1b2844
-- title:
--   P2 M Reciprocity Theory PGsh ATower  mul surj 156075eb5a76: P2 M Reciprocity Theory PGsh ATower  mul surj 156075eb5a76
-- statement:
--   The P2 M Reciprocity Theory PGsh ATower  mul surj 156075eb5a76 construction uses the P2 M Reciprocity Theory PGsh ATower  mul surj 156075eb5a76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/NsmulKerZero.lean#L17-L25

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
open ReciprocityTheory.PGsh.ATower
variable {p : ℕ} (Tw : ATower R₀ p)

theorem P2M_ReciprocityTheory_PGsh_ATower__mul_surj_156075eb5a76 (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by sorry

alias «ReciprocityTheory».«PGsh».«ATower».«ξmul_surj» := P2M_ReciprocityTheory_PGsh_ATower__mul_surj_156075eb5a76
