-- Prove2me | Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
-- name    : Section5PowerCode.codeSign_tilted_polynomial_mean
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:59.176211+00:00
-- url     : https://prove2.me/theorems/5721c44e-42ff-41c6-8d68-83f9f75c45b6
-- title:
--   Tilted polynomial moment matching for power-code signs
-- statement:
--   Let F be a finite field of characteristic two, χ a nontrivial real-valued additive character, and v:I→F injective on finite I. For uniform t∈F^k put c_i(t)=χ(Σ_{j<k}t_jv(i)^j). Let w∈R^I and P a real polynomial with total degree plus two at most k. Then $$\mathbb E_t[(\sum_iw_i c_i(t))^2P(c(t))]=\mathbb E_s[(\sum_iw_i s_i)^2P(s)],$$ where s has uniform independent signs. This is a finite moment identity.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CodedPolynomialMoments.lean, lines 45–52.

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedPolynomialMoments
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_product_sum_zero
import Theorems.Thm_Section5SignMoments_polynomial_mean_match
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

theorem Section5PowerCode.codeSign_tilted_polynomial_mean {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ)
    (p : MvPolynomial ι ℝ) (hp : p.totalDegree+2 ≤ k) :
    Section5SignMoments.mean (fun t : Fin k → F =>
      (∑ i, w i*Section5PowerCode.codeSign χ v t i)^2*MvPolynomial.eval (Section5PowerCode.codeSign χ v t) p)=
      Section5SignMoments.mean (fun x : ι → Bool =>
        (∑ i, w i*Section5BooleanFrame.sign x i)^2*
          MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by sorry
