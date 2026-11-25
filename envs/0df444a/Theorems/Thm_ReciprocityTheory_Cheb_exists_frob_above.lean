-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_frob_above
-- name    : ReciprocityTheory.Cheb.exists_frob_above
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:41.489939+00:00
-- url     : https://prove2.me/theorems/3fe4bc3e-e305-5e70-881b-04d20b9735a3
-- title:
--   Cheb: exists frob above
-- statement:
--   The Cheb construction uses the exists frob above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFrobE.lean#L7-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFrobE.lean#L7-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFrobE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.exists_frob_above {M : Type} [Field M] [NumberField M] (E : IntermediateField ℚ M) [IsGalois E M]
    (l : ℕ) [Fact l.Prime] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (q : Ideal (𝓞 E)) (hq : q.IsPrime)
    (hqp : (Ideal.absNorm q).Prime) (hql : Ideal.absNorm q ≠ l) :
    ∃ (P : Ideal (𝓞 M)) (_ : P.IsPrime) (φ : M ≃ₐ[E] M),
      P.LiesOver (Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)}) ∧ φ ζ = ζ ^ Ideal.absNorm q ∧
      IsArithFrobAt ℤ (φ.restrictScalars ℚ) P := by sorry
