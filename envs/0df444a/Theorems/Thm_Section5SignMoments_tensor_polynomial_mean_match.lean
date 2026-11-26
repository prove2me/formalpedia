-- Prove2me | Theorems.Thm_Section5SignMoments_tensor_polynomial_mean_match
-- name    : Section5SignMoments.tensor_polynomial_mean_match
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:14.046201+00:00
-- url     : https://prove2.me/theorems/ce78a2d4-5d5b-48dd-92ea-c71e9388ef38
-- title:
--   Tensorization of weighted polynomial moment matching
-- statement:
--   Let Ω,Ξ,I,J be finite, let a:Ω→R^I and b:Ξ→R^I, and let p_a,p_b be real weights. Assume all monomial weighted moments of total degree at most k agree. Then every real polynomial P on variables J×I of total degree at most k has equal product-weighted evaluations: $$\sum_{x\in\Omega^J}\left(\prod_rp_a(x_r)\right)P((a_i(x_r))_{r,i})=\sum_{y\in\Xi^J}\left(\prod_rp_b(y_r)\right)P((b_i(y_r))_{r,i}).$$ Positivity and normalization of the weights are not required.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TensorPolynomialMoments.lean, lines 33–40.

import Mathlib
set_option autoImplicit false
namespace Section5SignMoments
end Section5SignMoments
open Section5SignMoments
variable {ι J Ω Ξ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [Fintype Ω] [Fintype Ξ]

theorem Section5SignMoments.tensor_polynomial_mean_match (a : Ω → ι → ℝ) (b : Ξ → ι → ℝ)
    (pa : Ω → ℝ) (pb : Ξ → ℝ) (k : ℕ)
    (hm : ∀ d : ι →₀ ℕ, d.sum (fun _ e => e) ≤ k →
      (∑ x : Ω, pa x*(∏ i, a x i ^ d i))=
        ∑ y : Ξ, pb y*(∏ i, b y i ^ d i))
    (P : MvPolynomial (J × ι) ℝ) (hP : P.totalDegree ≤ k) :
    (∑ x : J → Ω, (∏ r, pa (x r))*MvPolynomial.eval (fun z => a (x z.1) z.2) P)=
      ∑ y : J → Ξ, (∏ r, pb (y r))*MvPolynomial.eval (fun z => b (y z.1) z.2) P := by sorry
