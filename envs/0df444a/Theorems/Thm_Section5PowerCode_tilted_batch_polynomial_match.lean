-- Prove2me | Theorems.Thm_Section5PowerCode_tilted_batch_polynomial_match
-- name    : Section5PowerCode.tilted_batch_polynomial_match
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:32.185891+00:00
-- url     : https://prove2.me/theorems/15e69cde-c829-58b2-b002-a42312e13bff
-- title:
--   Batch moment matching for tilted power-code frames
-- statement:
--   Let F be a finite characteristic-two field, χ nontrivial, v:I→F injective and J finite. Let D+2≤k, w∈R^I and P a polynomial on J×I of degree at most D. Let c(t) be the k-coefficient power-code signs and p_w(t)=|F|^(−k)(Σ_iw_ic_i(t))². Let s be uniform signs weighted by a_w(s)=2^(−|I|)(Σ_iw_is_i)². Then $$\sum_{t\in(F^k)^J}\prod_rp_w(t_r)P((c_i(t_r))_{r,i})=\sum_{s\in(\{\pm1\}^I)^J}\prod_ra_w(s_r)P((s_{ri})_{r,i}).$$ This is an exact weighted identity without a normalization assumption on w.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CodedBatchMoments.lean, lines 27–33.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
import Theorems.Thm_Section5SignMoments_tensor_polynomial_mean_match
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι J : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem Section5PowerCode.tilted_batch_polynomial_match {k D : ℕ} (hD : D+2 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (P : MvPolynomial (J × ι) ℝ) (hP : P.totalDegree ≤ D) :
    (∑ t : J → Fin k → F, (∏ r, Section5PowerCode.frameWeight χ v w (t r))*
      MvPolynomial.eval (fun z => Section5PowerCode.codeSign χ v (t z.1) z.2) P)=
      ∑ x : J → ι → Bool, (∏ r, Section5BooleanFrame.weight w (x r))*
        MvPolynomial.eval (fun z => Section5BooleanFrame.sign (x z.1) z.2) P := by sorry
