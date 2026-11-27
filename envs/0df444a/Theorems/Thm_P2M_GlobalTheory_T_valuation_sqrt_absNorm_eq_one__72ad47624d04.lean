-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_valuation_sqrt_absNorm_eq_one__72ad47624d04
-- name    : P2M_GlobalTheory_T_valuation_sqrt_absNorm_eq_one__72ad47624d04
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:53.608694+00:00
-- url     : https://prove2.me/theorems/1061f151-ab5e-453f-9f52-c77228ccc35a
-- title:
--   P2 M Global Theory T valuation sqrt abs Norm eq one  72ad47624d04: P2 M Global Theory T valuation sqrt abs Norm eq one  72ad47624d04
-- statement:
--   The P2 M Global Theory T valuation sqrt abs Norm eq one  72ad47624d04 construction uses the P2 M Global Theory T valuation sqrt abs Norm eq one  72ad47624d04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationSqrtAbsNormEqOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationSqrtAbsNormEqOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationSqrtAbsNormEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationSqrtAbsNormEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_valuation_sqrt_absNorm_eq_one__72ad47624d04 : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by sorry

alias «GlobalTheory».«T».«valuation_sqrt_absNorm_eq_one'» := P2M_GlobalTheory_T_valuation_sqrt_absNorm_eq_one__72ad47624d04
