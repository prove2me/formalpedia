-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_eq_32_feasible_sdp_optimization
-- name    : STOC2027BoolCSP.Approximation.eq_32_feasible_sdp_optimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:36.780466+00:00
-- url     : https://prove2.me/theorems/6e0ce36e-e119-4e31-9ab2-3ba0b1411414
-- title:
--   Section 7.1, equation (32) — exactly feasible rational SDP optimization
-- statement:
--   Fix $k\ge5$. For every normalized signed $k$-conjunction instance and every rational $0<\tau\le1$, one can compute a rational matrix $G\in\mathcal F$ with
--   $$f(G)\;\ge\;\mathrm{SDP}-\tau$$
--   in time polynomial in the explicit instance bit length and $\log(1/\tau)$. The output satisfies the affine equations of $\mathcal A$ exactly and is positive semidefinite. One fixed machine does this for all instances and all $\tau$.
--
--   This is the optimization step of the finite-bit algorithm. The paper derives it from the rational SDP optimization theorem of Grötschel–Lovász–Schrijver in the formulation of de Klerk–Vallentin, with the radii of Lemma 7.1, or from a weak optimizer followed by the repair (33).
--
--   Differences from the source:
--
--   - encoding: an algorithm (deterministic, polynomial time) → a fixed CoinMachine (Mathlib FinTM2 with finite stack alphabets and bit input/output stacks) run on the empty random tape, halting within P(1 + input length + precision) steps with the coded output; reason: ordinary finite-alphabet Turing computation, the model the paper's Section 7 names; one step is a bounded number of bit operations
--   - reading: time polynomial in the explicit instance bit length and log(1/τ) → steps ≤ P(1 + |code(C) ++ code(τ)| + p(τ)), p(τ) = max(0, ⌈log₂(1/τ)⌉); reason: the preamble of Section 1.1 states that the input length includes the representation of the accuracy parameter
--   - encoding: SDP, the optimum of (5) → sSup of the objective over the feasible Gram matrices; reason: the region is nonempty and compact (Section 3), so the supremum is the attained maximum
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 13 (PDF 16), Section 7.1, unnumbered displayed assertion, equation (32)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP

namespace STOC2027BoolCSP.Approximation

/-- Section 7.1, equation (32), printed p. 13: for normalized conjunction instances and every
rational `0 < τ ≤ 1`, one fixed machine computes, in time polynomial in the explicit input bit
length and `log(1/τ)`, a rational matrix `G ∈ 𝓕` (affine equations exact, positive
semidefinite) with `f(G) ≥ SDP − τ`. -/
theorem eq_32_feasible_sdp_optimization (k : ℕ) (hk : 5 ≤ k) :
    ∃ (Mach : CoinMachine) (P : Polynomial ℕ), ∀ C : ConjInstance k, C.Normalized →
      ∀ τ : ℚ, 0 < τ → τ ≤ 1 →
        ∃ G : Matrix (Idx C.n C.M) (Idx C.n C.M) ℚ,
          Mach.HaltsWithin (C.code ++ ratCode τ) []
            (P.eval (1 + (C.code ++ ratCode τ).length + precBits τ)) (gramCode G) ∧
          C.Feasible (ratToReal G) ∧
          C.sdpValue - τ ≤ C.objective (ratToReal G) := by sorry

end STOC2027BoolCSP.Approximation
