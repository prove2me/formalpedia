-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:55.250596+00:00
-- url     : https://prove2.me/theorems/d2fdfc74-6963-463c-b375-8e2076ff859e
-- title:
--   Cartwright Steger: is LSVFinite Det Candidate Spectrum Contained In Building Spectrum iff
-- statement:
--   Quantifier-level form of the finite-determinant-sector containment
--   candidate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L769-L780
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L769-L780

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsLSVFiniteDetCandidateSpectrumContainedInBuildingSpectrum P r level ↔
      ∀ eigenvalue vector,
        IsLSVJointEigenpair P r level eigenvalue vector →
        ¬ IsLSVFiniteDetCharacterVector P r level vector →
        eigenvalue ∈ lsvUniversalBuildingJointSpectrum P r := by sorry
