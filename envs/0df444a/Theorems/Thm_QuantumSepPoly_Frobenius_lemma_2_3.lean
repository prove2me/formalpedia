-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_2_3
-- name    : QuantumSepPoly.Frobenius.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:49.119297+00:00
-- url     : https://prove2.me/theorems/d6a38cf4-3873-4673-bb67-b965f6a893f7
-- title:
--   Lemma 2.3 — Complex Gaussian quadratic variance
-- statement:
--   Let $X$ be a standard complex Gaussian vector and let $T$ be any complex $d\times d$ matrix, with no Hermitian assumption. The squared deviation is integrable and
--   $$\mathbb E|X^*TX-\operatorname{Tr}T|^2=\|T\|_F^2.$$
--   This identifies the variance scale for arbitrary complex quadratic forms.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: expectation of the squared complex quadratic deviation → integrability as a conclusion together with the Bochner integral identity; reason: records the finiteness already implicit in the source expectation
--   - generalization: positive local dimension → also d=0; reason: the empty vector and operator give zero on both sides; every positive dimension remains included
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 2.3, p. 7 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Gaussian

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- Lemma 2.3, pp.7–8, including non-Hermitian operators. -/
theorem lemma_2_3 (d : ℕ) (T : Op d) :
  let f := fun g : (Fin d × Bool) → ℝ =>
    ‖(∑ i, ∑ j, star (complexGaussian g i) * T i j * complexGaussian g j) - T.trace‖^2
  Integrable f (realGaussian d) ∧ ∫ g, f g ∂realGaussian d = (frob T)^2 := by sorry

end QuantumSepPoly.Frobenius
