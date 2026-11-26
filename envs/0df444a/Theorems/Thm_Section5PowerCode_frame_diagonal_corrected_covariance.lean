-- Prove2me | Theorems.Thm_Section5PowerCode_frame_diagonal_corrected_covariance
-- name    : Section5PowerCode.frame_diagonal_corrected_covariance
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:26.378815+00:00
-- url     : https://prove2.me/theorems/38892faf-4906-53c2-8338-b54fea328554
-- title:
--   Corrected covariance of a power-code frame
-- statement:
--   Let F be a finite field of characteristic two, χ a nontrivial real additive character, v:I→F injective and k≥4. Let c_i(t)=χ(Σ_{j<k}t_jv(i)^j), p_w(t)=|F|^(−k)(Σ_iw_i c_i(t))² and Σ_iw_i²=1. For all i,j, $$\frac{\sum_t p_w(t)c_i(t)c_j(t)-\mathbf1_{i=j}}2+\mathbf1_{i=j}w_i^2=w_iw_j.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CodedFrameCovariance.lean, lines 49–53.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_covariance
import Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

theorem Section5PowerCode.frame_diagonal_corrected_covariance {k : ℕ} (hk : 4 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (hw : ∑ l, w l^2=1) (i j : ι) :
    ((∑ t : Fin k → F, Section5PowerCode.frameWeight χ v w t*(Section5PowerCode.codeSign χ v t i*Section5PowerCode.codeSign χ v t j))-
      (if i=j then 1 else 0))/2+(if i=j then w i^2 else 0)=w i*w j := by sorry
