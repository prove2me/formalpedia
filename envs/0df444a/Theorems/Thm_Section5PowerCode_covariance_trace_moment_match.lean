-- Prove2me | Theorems.Thm_Section5PowerCode_covariance_trace_moment_match
-- name    : Section5PowerCode.covariance_trace_moment_match
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:08.468796+00:00
-- url     : https://prove2.me/theorems/5f185eda-a882-56a1-9dcc-08fcaa010641
-- title:
--   Exact covariance trace-moment transfer for coded frames
-- statement:
--   Let F be a finite characteristic-two field, χ nontrivial, v:I→F injective and I,J finite. Let p,k be natural with 4p+2≤k, let w∈R^I and S be a real I×I matrix. For coded signs c(t), frame weights p_w(t)=|F|^(−k)(Σ_iw_ic_i(t))², and fully independent signs s weighted by a_w(s)=2^(−|I|)(Σ_iw_is_i)², form C_S(a)=|J|^(−1)Σ_ra_ra_r^T−S. Then $$\sum_t\prod_rp_w(t_r)\operatorname{tr}(C_S(c(t))^{2p})=\sum_s\prod_ra_w(s_r)\operatorname{tr}(C_S(s)^{2p}).$$ This transfers moments and does not itself establish an operator-norm tail bound.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CodedCovarianceTraceMoments.lean, lines 11–19.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
import Theorems.Thm_Section5PowerCode_tilted_batch_polynomial_match
import Theorems.Thm_Section5SignMoments_covarianceTracePolynomial_degree
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι J : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem Section5PowerCode.covariance_trace_moment_match {k : ℕ} (p : ℕ) (hp : 4*p+2 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (S : Matrix ι ι ℝ) :
    (∑ t : J → Fin k → F, (∏ r, Section5PowerCode.frameWeight χ v w (t r))*
      Matrix.trace ((Section5SignMoments.centeredCovariance S
        (fun r => Section5PowerCode.codeSign χ v (t r)))^(2*p)))=
      ∑ x : J → ι → Bool, (∏ r, Section5BooleanFrame.weight w (x r))*
        Matrix.trace ((Section5SignMoments.centeredCovariance S
          (fun r => Section5BooleanFrame.sign (x r)))^(2*p)) := by sorry
