-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_Supplement_fixed_rank_spectrum_estimation
-- name    : SingleCopyMoments.Adaptive.Supplement.fixed_rank_spectrum_estimation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:43:08.866533+00:00
-- url     : https://prove2.me/theorems/366275ee-8b99-4d38-99f4-522a49425ecb
-- title:
--   Theorem 28 — Fixed-rank full-spectrum upper bound
-- statement:
--   Fix $r\ge2$ and $\epsilon,\delta\in(0,1)$, and let $h=\lceil\log_2r\rceil$. There is a constant $C>0$, depending only on $r,\epsilon,\delta$, such that for every $d\ge1$ a single adaptive single-copy protocol and measurable sorted readout work for every $d$-dimensional state of rank at most $r$ and satisfy
--   $$T\le C d^{h/(h+1)},\qquad
--   \Pr\{\|\widehat\lambda-\operatorname{spec}(\rho)\|_1\le\epsilon\}\ge1-\delta.$$
--   The readout has $\min(r,d)$ nonincreasing nonnegative coordinates summing to one and is padded with zeros to length $d$ before comparison with the full sorted spectrum, including multiplicities. The law is normalized and the success event is measurable. This includes $d=1$, $r>d$, rank smaller than $r$, repeated eigenvalues and zero eigenvalues. No gap or lower bound on a nonzero eigenvalue is assumed.
--
--   This companion theorem estimates the complete spectrum. The all-positive-dimension formulation also covers the finitely many dimensions below an asymptotic threshold by single-copy tomography and enlargement of the same constant.
--
--   Differences from the source:
--   - generalization: asymptotic upper bound → one constant for all d>=1; reason: specializes to the stated asymptotic bound; d=1 is exact, and finite-dimensional single-copy tomography covers the finitely many remaining dimensions below the threshold after enlarging C
--   - encoding: full sorted spectrum → a min(r,d)-entry sorted probability output padded to d; reason: this is exactly the candidate representation and zero padding in the proof of Theorem 28
--   - encoding: probability of a successful estimate → normalized Born transcript law and measurable additive-success event; reason: makes the operational probability explicit without assuming successful estimation
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Theorem 28, printed p. 29 (PDF p. 31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Supplement_Spectra

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- Theorem 28, printed p.29 / PDF p.31; output includes all d eigenvalues. -/
theorem fixed_rank_spectrum_estimation (r : ℕ) (hr : 2 ≤ r)
    (ε δ : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C > (0 : ℝ), ∀ d : ℕ, 0 < d →
    ∃ T : ℕ, ∃ P : Protocol d, ∃ out : Record P → SortedProbVec (min r d),
      (T : ℝ) ≤ C * (d : ℝ) ^ exponent r ∧ SpectrumSucceeds P T r out ε δ := by sorry

end SingleCopyMoments.Adaptive.Supplement
