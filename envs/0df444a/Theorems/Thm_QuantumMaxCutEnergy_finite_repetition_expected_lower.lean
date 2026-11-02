-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_finite_repetition_expected_lower
-- name    : QuantumMaxCutEnergy.finite_repetition_expected_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T14:26:00.369198+00:00
-- url     : https://prove2.me/theorems/310f13b2-d5e0-47fb-91d2-7a27c93e255b
-- title:
--   Exact finite-sampling amplification for a numerical lower estimate
-- statement:
--   Let Ω be any nonempty finite sample space and X a real-valued one-trial estimate. Draw k independent uniform samples from Ω. Suppose a nonnegative output Y dominates each of the k sampled values of X. If q is the exact fraction of one-trial samples with X<t, then the uniform mean of Y is at least t(1−q^k). This includes k=0 and arbitrary real thresholds t. The theorem is a finite probability and expectation statement; it asserts no algorithm or running-time bound.
-- source:
--   Derived finite probability lemma for the independent-repetition step in Anshu, Gosset and Morenz, TQC2020, p7:10, paragraph between Eqs29 and30. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The explicit exact finite-sample expectation formula is a formal supporting derivation, not a verbatim numbered theorem in the source.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators

theorem QuantumMaxCutEnergy.finite_repetition_expected_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) (k : ℕ)
    (Y : (Fin k → Ω) → ℝ)
    (hY : ∀ s, 0 ≤ Y s)
    (hmax : ∀ s i, X (s i) ≤ Y s) :
    t * (1 - (((Finset.univ.filter (fun ω => ¬ t ≤ X ω)).card : ℝ) /
      (Fintype.card Ω : ℝ)) ^ k) ≤
      (∑ s, Y s) / (Fintype.card (Fin k → Ω) : ℝ) := by sorry
