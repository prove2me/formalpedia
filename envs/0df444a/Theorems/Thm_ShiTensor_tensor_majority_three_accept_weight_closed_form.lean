-- Prove2me | Theorems.Thm_ShiTensor_tensor_majority_three_accept_weight_closed_form
-- name    : ShiTensor.tensor_majority_three_accept_weight_closed_form
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T08:03:47.591243+00:00
-- url     : https://prove2.me/theorems/2d8b195c-19e7-48aa-b6a0-144a78cfa405
-- title:
--   Three-copy majority accept-weight equals 3p^2 - 2p^3
-- statement:
--   The bridge from a three-copy quantum accept-weight to a combinatorial closed form. Three amplitude arrays on M, P and Q bits are combined into the right-nested product state tensor psi (tensor phi chi) on M + (P + Q) bits, so the second block's bits are read by leftBits of rightBits and the third block's by rightBits of rightBits. Each block carries a Boolean accept predicate, and the theorem computes the total squared-amplitude weight of the joint outcomes at which AT LEAST TWO of the three predicates fire. That weight is exactly 3 p squared minus 2 p cubed, which is majProb 3 p by the separately accepted ShiAmp.majProb_three. majProb cannot be NAMED here because the amplitude-tensor file does not import the amplification definitions -- the two live on different import towers -- so the conclusion is stated as the bare closed form and the identification is made in this prose rather than in the statement.
--
--   ROUTE. The majority guard couples the three blocks, so it does not factor. Pointwise, the guarded weight is rewritten as an indicator times the weight, and the indicator is expanded by inclusion-exclusion into the three pairwise products minus twice the triple product. A Boolean case bash turns that polynomial back into four guarded terms whose guards are CONJUNCTIONS, with the constant-true predicate filling the don't-care slot. Each of the four sums then factors into a product of three per-block sums by applying the two-sided factorisation twice, once splitting M from P + Q and once splitting P from Q. The don't-care factor becomes the block's total weight 1, the others become p, giving p*p + p*p + p*p - 2 p cubed, which ring closes.
--
--   PROVENANCE. hJoint abstracts the separately accepted ShiTensor.outDist_tensor_joint_factor, with the two block sizes made explicit binders and renamed so as not to clash with the probability p. hIE abstracts the separately accepted ShiAmp.majority3_indicator_inclusion_exclusion. Nothing else is assumed.
--
--   HONEST LIMITATIONS. There is NO measure theory anywhere: these are finite sums over Bits, with no PMF and no product measure, and the independence that makes the weights multiply is a structural consequence of the definition of tensor, not a probabilistic hypothesis. The per-block accept weight being exactly p and each block's total weight being exactly 1 are HYPOTHESES, not derived facts; no normalisation or unitarity is proved, and the three arrays are arbitrary complex-valued. Nothing here claims that 3 p squared minus 2 p cubed exceeds p, or is monotone, or amplifies anything -- that is the separately accepted contraction analysis. No universality claim is made for the H/S/T/X/CNOT gate set, and nothing connects these accept-weights to circuit dynamics. In particular the majority READOUT circuit, proved separately from three Toffoli gates, is not built or referenced here: this statement is about accept-weights only.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem tensor_majority_three_accept_weight_closed_form (M P Q : ℕ) (p : ℝ)
    (ψ : QState M) (φ : QState P) (χ : QState Q)
    (f : Bits M → Bool) (g : Bits P → Bool) (h : Bits Q → Bool)
    (hJoint : ∀ (m n : ℕ) (a : QState m) (b : QState n)
      (u : Bits m → Bool) (v : Bits n → Bool),
      ∑ y : Bits (m + n), (if u (leftBits y) && v (rightBits y)
          then ‖tensor a b y‖ ^ 2 else 0)
        = (∑ s : Bits m, (if u s then ‖a s‖ ^ 2 else 0))
          * ∑ t : Bits n, (if v t then ‖b t‖ ^ 2 else 0))
    (hIE : ∀ b1 b2 b3 : Bool,
      (if 2 ≤ (if b1 then (1 : ℕ) else 0) + (if b2 then (1 : ℕ) else 0)
            + (if b3 then (1 : ℕ) else 0) then (1 : ℝ) else 0)
        = (if b1 then (1 : ℝ) else 0) * (if b2 then (1 : ℝ) else 0)
          + (if b2 then (1 : ℝ) else 0) * (if b3 then (1 : ℝ) else 0)
          + (if b3 then (1 : ℝ) else 0) * (if b1 then (1 : ℝ) else 0)
          - 2 * ((if b1 then (1 : ℝ) else 0) * (if b2 then (1 : ℝ) else 0)
              * (if b3 then (1 : ℝ) else 0)))
    (hfp : ∑ a : Bits M, (if f a then ‖ψ a‖ ^ 2 else 0) = p)
    (hgp : ∑ b : Bits P, (if g b then ‖φ b‖ ^ 2 else 0) = p)
    (hhp : ∑ c : Bits Q, (if h c then ‖χ c‖ ^ 2 else 0) = p)
    (hψ1 : ∑ a : Bits M, ‖ψ a‖ ^ 2 = 1)
    (hφ1 : ∑ b : Bits P, ‖φ b‖ ^ 2 = 1)
    (hχ1 : ∑ c : Bits Q, ‖χ c‖ ^ 2 = 1) :
    ∑ y : Bits (M + (P + Q)),
      (if 2 ≤ (if f (leftBits y) then (1 : ℕ) else 0)
            + (if g (leftBits (rightBits y)) then (1 : ℕ) else 0)
            + (if h (rightBits (rightBits y)) then (1 : ℕ) else 0)
        then ‖tensor ψ (tensor φ χ) y‖ ^ 2 else 0)
      = 3 * p ^ 2 - 2 * p ^ 3 := by
  sorry

end ShiTensor
