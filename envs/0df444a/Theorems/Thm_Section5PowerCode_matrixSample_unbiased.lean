-- Prove2me | Theorems.Thm_Section5PowerCode_matrixSample_unbiased
-- name    : Section5PowerCode.matrixSample_unbiased
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:07.594295+00:00
-- url     : https://prove2.me/theorems/086fb132-1e1f-4ce8-b00e-af46dd9affee
-- title:
--   Unbiased corrected matrix sample from power-code outcomes
-- statement:
--   Let F be a finite field of characteristic two, χ nontrivial, v:I→F injective, k≥4 and Σ_iw_i²=1. Let t have frame weight p_w(t)=|F|^(−k)(Σ_iw_i c_i(t))² and independently let y have probability w_y², where c_i(t)=χ(Σ_{j<k}t_jv(i)^j). Define M_ij(t,y)=(c_i(t)c_j(t)−1_(i=j))/2+1_(i=j=y). Then $$\mathbb E[M_{ij}]=w_iw_j.$$ This unbiasedness identity alone does not assert matrix concentration or a quantum learning algorithm.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5CodedFrameEstimator.lean, lines 51–54.

import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5CodedFrameEstimator
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
import Theorems.Thm_Section5PowerCode_frameWeight_sum
import Theorems.Thm_Section5PowerCode_frame_diagonal_corrected_covariance
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

theorem Section5PowerCode.matrixSample_unbiased {k : ℕ} (hk : 4 ≤ k) (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ) (hw : ∑ i, w i^2=1)
    (i j : ι) :
    (∑ z : (Fin k → F) × ι, Section5PowerCode.jointWeight χ v w z*Section5PowerCode.matrixSample χ v z.1 z.2 i j)=w i*w j := by sorry
