-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JacobiTriple_tendsto_finCoeff_sum_jacobiTheta__05d3059cb3f7
-- name    : P2M_GlobalTheory_JacobiTriple_tendsto_finCoeff_sum_jacobiTheta__05d3059cb3f7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:41:02.38745+00:00
-- url     : https://prove2.me/theorems/1cc20c1e-b0a5-5fe2-8681-021ca9b48304
-- title:
--   P2 M Global Theory Jacobi Triple tendsto fin Coeff sum jacobi Theta  05d3059cb3f7: P2 M Global Theory Jacobi Triple tendsto fin Coeff sum jacobi Theta  05d3059cb3f7
-- statement:
--   The P2 M Global Theory Jacobi Triple tendsto fin Coeff sum jacobi Theta  05d3059cb3f7 construction uses the P2 M Global Theory Jacobi Triple tendsto fin Coeff sum jacobi Theta  05d3059cb3f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleProductLimit.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleProductLimit.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
open GlobalTheory GlobalTheory.JacobiTriple

theorem P2M_GlobalTheory_JacobiTriple_tendsto_finCoeff_sum_jacobiTheta__05d3059cb3f7 : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im →
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
      GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ)
      Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by sorry

alias «GlobalTheory».«JacobiTriple».«tendsto_finCoeff_sum_jacobiTheta₂» := P2M_GlobalTheory_JacobiTriple_tendsto_finCoeff_sum_jacobiTheta__05d3059cb3f7
