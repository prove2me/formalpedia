-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exc_of_dvd_c4fb5d0e0daf
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_exc_of_dvd_c4fb5d0e0daf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:55.493731+00:00
-- url     : https://prove2.me/theorems/14e27371-0297-4c6b-a840-8b15e0d1f087
-- title:
--   P2 M Formalism Basic Notions Examples  NZ exc of dvd c4fb5d0e0daf: P2 M Formalism Basic Notions Examples  NZ exc of dvd c4fb5d0e0daf
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ exc of dvd c4fb5d0e0daf construction uses the P2 M Formalism Basic Notions Examples  NZ exc of dvd c4fb5d0e0daf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeA.lean#L42-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeA.lean#L42-L104

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms

theorem P2M_Formalism_BasicNotions_Examples__NZ_exc_of_dvd_c4fb5d0e0daf {g d e ℓ c : ℕ} (hg : 2 ≤ g) (hℓ : ℓ.Prime) (hd : 1 ≤ d) (he : 2 * Nat.gcd d e ≤ d)
    (h : g ^ d - 1 ∣ ℓ ^ c * (g ^ e - 1)) : Exc g d ℓ := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«exc_of_dvd» := P2M_Formalism_BasicNotions_Examples__NZ_exc_of_dvd_c4fb5d0e0daf
