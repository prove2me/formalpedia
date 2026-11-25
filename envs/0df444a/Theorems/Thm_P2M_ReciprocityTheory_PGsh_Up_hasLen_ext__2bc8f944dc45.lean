-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_hasLen_ext__2bc8f944dc45
-- name    : P2M_ReciprocityTheory_PGsh_Up_hasLen_ext__2bc8f944dc45
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:43:37.319917+00:00
-- url     : https://prove2.me/theorems/fdbc63fe-3490-5a56-bd8c-c67012389974
-- title:
--   P2 M Reciprocity Theory PGsh Up has Len ext  2bc8f944dc45: P2 M Reciprocity Theory PGsh Up has Len ext  2bc8f944dc45
-- statement:
--   The P2 M Reciprocity Theory PGsh Up has Len ext  2bc8f944dc45 construction uses the P2 M Reciprocity Theory PGsh Up has Len ext  2bc8f944dc45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenCokerDet.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/HasLenCokerDet.lean#L46-L52

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up

theorem P2M_ReciprocityTheory_PGsh_Up_hasLen_ext__2bc8f944dc45 {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R)
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) := by sorry

alias «ReciprocityTheory».«PGsh».«Up».«hasLen_ext'» := P2M_ReciprocityTheory_PGsh_Up_hasLen_ext__2bc8f944dc45
