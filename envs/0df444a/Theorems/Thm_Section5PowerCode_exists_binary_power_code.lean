-- Prove2me | Theorems.Thm_Section5PowerCode_exists_binary_power_code
-- name    : Section5PowerCode.exists_binary_power_code
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:17.853281+00:00
-- url     : https://prove2.me/theorems/854a08f1-3453-487d-830b-52e196caf1ed
-- title:
--   Existence of binary power codes with bounded polynomial moments
-- statement:
--   Let r>0, n≤2^r and k natural. There exist a nontrivial real additive character χ of F_(2^r) and an injection v:{1,…,n}→F_(2^r) such that, writing c_i(t)=χ(Σ_{j<k}t_jv(i)^j), every real polynomial P of total degree at most k satisfies $$\mathbb E_{t\in F_{2^r}^k}P(c(t))=\mathbb E_{s\in\{\pm1\}^n}P(s).$$ This asserts exact moments, without a sampling circuit or concentration guarantee.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5BinaryPowerCode.lean, lines 19–25.

import Definitions.Def_Section5Verified_Section5BinaryPowerCode
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_product_sum_zero
import Theorems.Thm_Section5PowerCode_exists_binary_field_character
import Theorems.Thm_Section5SignMoments_polynomial_mean_match
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode

theorem Section5PowerCode.exists_binary_power_code {n r : ℕ} (hr : r ≠ 0) (hn : n ≤ 2^r) (k : ℕ) :
    ∃ (χ : AddChar (GaloisField 2 r) ℝ) (v : Fin n ↪ GaloisField 2 r), χ ≠ 0 ∧
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ k →
        Section5SignMoments.mean (fun t : Fin k → GaloisField 2 r =>
          MvPolynomial.eval (Section5PowerCode.codeSign χ v t) p)=
        Section5SignMoments.mean (fun x : Fin n → Bool =>
          MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by sorry
