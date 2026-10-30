-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_uniform_schur_and_word_count
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.uniform_schur_and_word_count
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:50:14.905826+00:00
-- url     : https://prove2.me/theorems/77cf6d37-4691-4d0c-8ea4-8dadd2002037
-- title:
--   Remark 2.27
-- statement:
--   For $d\ge1$, $n\ge0$, and $\lambda\vdash n$ of height at most $d$, let $p_\lambda$ be its Specht module and $q_\lambda^d$ its unitary-group module. Then
--
--   $$\mathrm{SW}_d^n(\lambda)=d^{-n}\dim p_\lambda\dim q_\lambda^d,$$
--   $$\#\{w\in[d]^n:\operatorname{RSK}(w)=\lambda\}=\dim p_\lambda\dim q_\lambda^d.$$
--
--   The count concerns whole words, and the two representation dimensions are kept distinct. This turns Schur mass formulas into exact combinatorial counts.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 22, Remark 2.27

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Remark 2.27, arXiv:1501.05028v1, PDF p.22.  -/
theorem uniform_schur_and_word_count
    (d n : ℕ) (hd : 0 < d) (lambda : Schur.Partition d n) :
    swSpectrum (unif d) lambda = (dim lambda.val : ℝ) *
      (Module.finrank ℂ (Schur.schurModule lambda) : ℝ) / (d : ℝ)^n ∧
    (Finset.univ.filter fun w : Fin n → Fin d => rsk w = lambda.val).card =
      dim lambda.val * Module.finrank ℂ (Schur.schurModule lambda) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
