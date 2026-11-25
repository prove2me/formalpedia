-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_step1
-- name    : ReciprocityTheory.PGsh.BX.step1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:10.853816+00:00
-- url     : https://prove2.me/theorems/faf3ef8f-b210-4f2a-bb9f-fd1d77aebd11
-- title:
--   BX: step1
-- statement:
--   The BX construction uses the step1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L120-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/TotalFibreMapTotalFibreNsmulSnd.lean#L120-L349

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
import Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span

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
variable (B : BX R₀)

theorem ReciprocityTheory.PGsh.BX.step1 {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)
    (hB2 : HighestWeightVectorUniformBounds B) (N : ℕ) (hN : (N : (R' : Type u)) = 0) :
    ∃ O : ∀ V W : B.gg ⊗[R₀] π.ker, B.P R' (B.tg π (π.sqZero_of_span ξ hsurj hker hsq) V)
        (B.tg π (π.sqZero_of_span ξ hsurj hker hsq) W),
      (∀ V W, B.sw (O V W) = O W V) ∧
      ∀ (V W : B.gg ⊗[R₀] π.ker) (th : B.G R') (h : B.gg →ₗ[R₀] (R' : Type u))
        (hW : N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) W),
        B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ h) →
        ∀ u : B.P R' (B.tg π (π.sqZero_of_span ξ hsurj hker hsq) V) th,
        HEq (B.pmap π u) (B.zero1 (B.map π th)) →
        ∃ c : (R' : Type u)ˣ, (c : (R' : Type u)) = 1 - B.evK π h V ∧
          B.tr2 hW (B.nsmul2 u N) = B.smul c (O V W) := by sorry
