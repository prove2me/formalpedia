-- Prove2me | Theorems.Thm_PI_SqPair_LCP_assemble
-- name    : PI.SqPair.LCP.assemble
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:23:55.396792+00:00
-- url     : https://prove2.me/theorems/5e36e328-5642-45da-b45f-c97ca788f132
-- title:
--   LCP: assemble
-- statement:
--   The LCP construction uses the assemble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L34-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean#L34-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
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
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R]

theorem PI.SqPair.LCP.assemble {κ : Type} [Fintype κ] [DecidableEq κ]
    (A h u u' : Matrix (Fin 2 ⊕ κ) (Fin 2 ⊕ κ) R) (A₁ h₂ : Matrix κ κ R) (d : Fin 2 → R)
    (hu : IsUnit u.det) (hu' : IsUnit u'.det)
    (hA : uᴴ * A * u = fromBlocks hyp 0 0 A₁)
    (hh : h * u' = u * fromBlocks (diagonal d) 0 0 h₂)
    (e₂ f₂ : Matrix κ κ R) (he : e₂ * e₂ = e₂) (heA : e₂ᴴ * A₁ = A₁ * (1 - e₂))
    (hef : e₂ * h₂ = h₂ * f₂) : PConcl A h := by sorry
