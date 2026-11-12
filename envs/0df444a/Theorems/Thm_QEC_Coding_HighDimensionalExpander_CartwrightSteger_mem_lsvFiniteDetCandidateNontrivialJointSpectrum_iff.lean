-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:30.408021+00:00
-- url     : https://prove2.me/theorems/5e776230-1015-48ec-8a78-3c638e903ec2
-- title:
--   Cartwright Steger: mem lsv Finite Det Candidate Nontrivial Joint Spectrum iff
-- statement:
--   The Cartwright Steger construction uses the mem lsv Finite Det Candidate Nontrivial Joint Spectrum iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L758-L765
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L758-L765

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_lsvFiniteDetCandidateNontrivialJointSpectrum_iff
    (P : BasePrime) (r : Rank) (level : Nat)
    (eigenvalue : Fin (r.matrixRank - 1) → ℂ) :
    eigenvalue ∈ lsvFiniteDetCandidateNontrivialJointSpectrum P r level ↔
      ∃ vector,
        IsLSVJointEigenpair P r level eigenvalue vector ∧
          ¬ IsLSVFiniteDetCharacterVector P r level vector := by sorry
