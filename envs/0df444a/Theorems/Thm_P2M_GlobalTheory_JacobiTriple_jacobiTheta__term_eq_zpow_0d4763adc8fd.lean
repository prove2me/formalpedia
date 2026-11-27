-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JacobiTriple_jacobiTheta__term_eq_zpow_0d4763adc8fd
-- name    : P2M_GlobalTheory_JacobiTriple_jacobiTheta__term_eq_zpow_0d4763adc8fd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:33.704705+00:00
-- url     : https://prove2.me/theorems/814b0246-204d-4a3a-81cb-f9ed5233a76d
-- title:
--   P2 M Global Theory Jacobi Triple jacobi Theta  term eq zpow 0d4763adc8fd: P2 M Global Theory Jacobi Triple jacobi Theta  term eq zpow 0d4763adc8fd
-- statement:
--   The P2 M Global Theory Jacobi Triple jacobi Theta  term eq zpow 0d4763adc8fd construction uses the P2 M Global Theory Jacobi Triple jacobi Theta  term eq zpow 0d4763adc8fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultipliableTpFactor.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultipliableTpFactor.lean#L48-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.JacobiTriple

theorem P2M_GlobalTheory_JacobiTriple_jacobiTheta__term_eq_zpow_0d4763adc8fd (τ z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = cexp (2 * π * I * z) ^ j * cexp (π * I * τ) ^ (j ^ 2) := by sorry

alias «GlobalTheory».«JacobiTriple».«jacobiTheta₂_term_eq_zpow» := P2M_GlobalTheory_JacobiTriple_jacobiTheta__term_eq_zpow_0d4763adc8fd
