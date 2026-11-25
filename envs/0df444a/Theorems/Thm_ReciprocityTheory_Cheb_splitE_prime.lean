-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitE_prime
-- name    : ReciprocityTheory.Cheb.splitE_prime
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:49:13.807136+00:00
-- url     : https://prove2.me/theorems/db556cf6-b7da-5dcb-acec-6cc5da4c462f
-- title:
--   Cheb: split E prime
-- statement:
--   The Cheb construction uses the split E prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L77-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L77-L136

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem ReciprocityTheory.Cheb.splitE_prime (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver q.asIdeal] :
    Q.ramificationIdx (𝓞 E) = 1 ∧ Q.inertiaDeg (𝓞 E) = 1 ∧ Ideal.absNorm Q = Nrm q := by sorry
