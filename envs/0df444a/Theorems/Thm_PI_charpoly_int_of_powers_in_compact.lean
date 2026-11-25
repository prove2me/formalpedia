-- Prove2me | Theorems.Thm_PI_charpoly_int_of_powers_in_compact
-- name    : PI.charpoly_int_of_powers_in_compact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:44.721167+00:00
-- url     : https://prove2.me/theorems/69594063-9d1c-4cf0-8508-d4881722b550
-- title:
--   PI: charpoly int of powers in compact
-- statement:
--   The PI construction uses the charpoly int of powers in compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicFiniteOrder/Assembly.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicFiniteOrder/Assembly.lean#L10-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicFiniteOrder_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI
open NumberField IsDedekindDomain TensorProduct Matrix

theorem PI.charpoly_int_of_powers_in_compact (hT : TensCpctDen) (hP : PowBddInt)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ)
    (γ : Matrix (Fin k) (Fin k) E) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    (∀ (n : ℕ) (i j : Fin k), inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((γ ^ n) i j) ∈ C) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i) := by sorry
