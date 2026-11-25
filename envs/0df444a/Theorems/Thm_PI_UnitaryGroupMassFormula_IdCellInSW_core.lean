-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_core
-- name    : PI.UnitaryGroupMassFormula.IdCellInSW.core
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:53.626481+00:00
-- url     : https://prove2.me/theorems/98e83747-19d2-4ba0-908b-013371337807
-- title:
--   Id Cell In SW: core
-- statement:
--   The Id Cell In SW construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdentityCellTrace/AlgIdentity.lean#L56-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdentityCellTrace/AlgIdentity.lean#L56-L292

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_AlgIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]

theorem PI.UnitaryGroupMassFormula.IdCellInSW.core (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (hU : Formalism.HermitianLatticesTheory.dual h Λ = Λ)
    (X : Submodule E V) (hiso : ∀ x ∈ X, ∀ y ∈ X, h x y = 0) {r : ℕ}
    (e e' : Fin r → V) (he : ∀ a, e a ∈ X) (he' : ∀ a, e' a ∈ X)
    (c c' : Fin r → V → E)
    (hc : ∀ x ∈ X, x = ∑ a, c a x • e a) (hc' : ∀ x ∈ X, x = ∑ a, c' a x • e' a)
    (hcadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c a (x + y) = c a x + c a y)
    (hcadd' : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c' a (x + y) = c' a x + c' a y)
    (hcsmul : ∀ a (t : E), ∀ x ∈ X, c a (t • x) = t * c a x)
    (hcsmul' : ∀ a (t : E), ∀ x ∈ X, c' a (t • x) = t * c' a x)
    (hδ : ∀ a b, c a (e b) = if a = b then 1 else 0) (hδ' : ∀ a b, c' a (e' b) = if a = b then 1 else 0)
    (J : Fin r → Submodule (𝓞 E) E)
    (hJ1 : ∀ a, ∀ t ∈ J a, t • e a ∈ Λ ∧ t • e' a ∈ Λ)
    (hJ2 : ∀ x ∈ Λ, x ∈ X → ∀ a, c a x ∈ J a ∧ c' a x ∈ J a)
    (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) :
    ∃ n : V ≃ₗ[E] V, n ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ ∧ (∀ a, n (e a) = e' a) ∧
      ∀ v, (∀ x ∈ X, h x v = 0) → n v - v ∈ X := by sorry
