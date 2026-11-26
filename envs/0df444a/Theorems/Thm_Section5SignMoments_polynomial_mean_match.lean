-- Prove2me | Theorems.Thm_Section5SignMoments_polynomial_mean_match
-- name    : Section5SignMoments.polynomial_mean_match
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:18.843642+00:00
-- url     : https://prove2.me/theorems/6aed3843-4345-4cdc-a977-1b63297a7dfd
-- title:
--   Polynomial mean transfer from bounded sign moments
-- statement:
--   Let Ω and I be finite, and let a:Ω→R^I satisfy a_i(x)²=1. Suppose for every S⊆I with |S|≤k its uniform product moment is zero for nonempty S and one for empty S. For every real multivariate polynomial P of total degree at most k, $$\mathbb E_{x\in\Omega}P(a(x))=\mathbb E_{s\in\{\pm1\}^I}P(s).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SignMomentTransfer.lean, lines 86–91.

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
set_option autoImplicit false
namespace Section5SignMoments
end Section5SignMoments
open Section5SignMoments
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

theorem Section5SignMoments.polynomial_mean_match (a : Ω → ι → ℝ) (ha : ∀ x i, a x i ^ 2=1) (k : ℕ)
    (hm : ∀ S : Finset ι, S.card ≤ k →
      Section5SignMoments.mean (fun x => ∏ i ∈ S, a x i)=if S=∅ then 1 else 0)
    (p : MvPolynomial ι ℝ) (hp : p.totalDegree ≤ k) :
    Section5SignMoments.mean (fun x => MvPolynomial.eval (a x) p)=
      Section5SignMoments.mean (fun x : ι → Bool => MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by sorry
