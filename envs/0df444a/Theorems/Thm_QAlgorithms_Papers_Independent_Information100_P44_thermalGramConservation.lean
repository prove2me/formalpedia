-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_thermalGramConservation
-- name    : QAlgorithms.Papers.Independent.Information100.P44.thermalGramConservation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:34:11.408428+00:00
-- url     : https://prove2.me/theorems/68727621-c055-42ec-b2dd-f2c125447483
-- title:
--   Lemma 1: thermal Gram conservation
-- statement:
--   For a thermal operation on a nonzero finite-dimensional system, choose any one finite nonempty bath dilation and its shell vectors $w_{r|i}$. At the same real inverse temperature, let $\gamma_i$ be the normalized per-basis Gibbs weights. For all input and output basis labels,
--   $$\sum_r\langle w_{r|j},w_{r|i}\rangle=\delta_{ij},\qquad \sum_i\gamma_i\langle w_{s|i},w_{r|i}\rangle=\gamma_r\delta_{rs}.$$
--   These identities include unequal-energy pairs; the relevant inner products then vanish by shell support. They express thermal Gram conservation without an equal-energy restriction.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 9, Lemma 1: thermal Gram conservation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.9, Lemma 1: Gram conservation, including unequal-energy pairs. -/
theorem thermalGramConservation {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) :
    (∀ i j, (∑ r, inner ℂ (shellVector D r j) (shellVector D r i)) =
      if i = j then 1 else 0) ∧
    (∀ r s, (∑ i, (gibbsWeight E beta i : ℂ) *
      inner ℂ (shellVector D s i) (shellVector D r i)) =
        if r = s then (gibbsWeight E beta r : ℂ) else 0) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
