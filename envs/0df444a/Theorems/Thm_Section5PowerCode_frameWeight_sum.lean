-- Prove2me | Theorems.Thm_Section5PowerCode_frameWeight_sum
-- name    : Section5PowerCode.frameWeight_sum
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:11.415339+00:00
-- url     : https://prove2.me/theorems/efe07d25-c4ff-545a-92fb-e1c6f092a12e
-- title:
--   Normalization of power-code frame weights
-- statement:
--   Let F be a finite field of characteristic two, χ a nontrivial real additive character, v:I→F injective and k≥2. For t∈F^k set c_i(t)=χ(Σ_{j<k}t_jv(i)^j) and p_w(t)=|F|^(−k)(Σ_iw_i c_i(t))². For every real w, $$\sum_t p_w(t)=\sum_iw_i^2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CodedFrameCovariance.lean, lines 19–21.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

theorem Section5PowerCode.frameWeight_sum {k : ℕ} (hk : 2 ≤ k) (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ) :
    (∑ t : Fin k → F, Section5PowerCode.frameWeight χ v w t)=∑ i, w i^2 := by sorry
