-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_lemma_7_1
-- name    : STOC2027BoolCSP.Approximation.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:50.017642+00:00
-- url     : https://prove2.me/theorems/5435d6c9-74b9-4786-a9b0-59110aaa34dd
-- title:
--   Lemma 7.1 — quantitative rational interior point
-- statement:
--   Fix $k\ge5$ and put $m=k+1$. For a signed $k$-conjunction instance with $n$ variables and $M$ clauses let $D=n+1+M$, and let $\mathcal A$ and $\mathcal F$ be as in Section 7.1. The affine slice $\mathcal F$ contains an explicitly computable rational matrix $G_0$ with
--   $$G_0\succeq\lambda I_D,\qquad \lambda=\frac1{2M+4m},$$
--   whose entries have polynomial bit length. With $\mathcal L=\mathcal A-G_0$,
--   $$G_0+\{E\in\mathcal L:\|E\|_F\le\lambda/2\}\;\subseteq\;\mathcal F\;\subseteq\;G_0+\{E\in\mathcal L:\|E\|_F\le2D\}.$$
--   Explicit computability is uniform: one fixed machine computes $G_0$ from the code of every instance in time polynomial in its length.
--
--   These radii are the rationality and quantitative-interior hypotheses of the rational SDP optimization theorem used in equation (32).
--
--   Differences from the source:
--
--   - generalization: Section 7 standing assumption: expanded weights sum to one → every conjunction instance, any rational weights; reason: 𝒜, 𝓕, G₀ and both radii do not involve the weights; the normalized instances are a special case
--   - encoding: explicitly computable rational G₀ with entries of polynomial bit length → a fixed CoinMachine on the empty tape outputs the code of G₀ within P(1 + code length) steps, and every entry code has length ≤ P(1 + code length); reason: ordinary finite-alphabet Turing computation, the model the paper's Section 7 names; one step is a bounded number of bit operations
--   - encoding: L = 𝒜 − G₀ → perturbations E with G₀ + E ∈ 𝒜; reason: identical sets
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 13 (PDF 16), Lemma 7.1

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP

namespace STOC2027BoolCSP.Approximation

/-- Lemma 7.1 (quantitative rational interior point), printed p. 13: one fixed machine computes,
from the code of any conjunction instance, a rational matrix `G₀ ∈ 𝓕` with `G₀ ⪰ λ I_D`,
`λ = 1/(2M + 4m)`, `m = k + 1`, entries of polynomial bit length, and
`G₀ + {E ∈ L : ‖E‖_F ≤ λ/2} ⊆ 𝓕 ⊆ G₀ + {E ∈ L : ‖E‖_F ≤ 2D}`, `L = 𝒜 − G₀`, `D = n + 1 + M`. -/
theorem lemma_7_1 (k : ℕ) (hk : 5 ≤ k) :
    ∃ (Mach : CoinMachine) (P : Polynomial ℕ), ∀ C : ConjInstance k,
      ∃ G₀ : Matrix (Idx C.n C.M) (Idx C.n C.M) ℚ,
        Mach.HaltsWithin C.code [] (P.eval (1 + C.code.length)) (gramCode G₀) ∧
        (∀ i j, (ratCode (G₀ i j)).length ≤ P.eval (1 + C.code.length)) ∧
        C.Feasible (ratToReal G₀) ∧
        (ratToReal G₀ - ((1 : ℝ) / (2 * C.M + 4 * (k + 1))) • (1 : Matrix _ _ ℝ)).PosSemidef ∧
        (∀ E : Matrix (Idx C.n C.M) (Idx C.n C.M) ℝ, C.InAffine (ratToReal G₀ + E) →
          frobNorm E ≤ ((1 : ℝ) / (2 * C.M + 4 * (k + 1))) / 2 → C.Feasible (ratToReal G₀ + E)) ∧
        (∀ G : Matrix (Idx C.n C.M) (Idx C.n C.M) ℝ, C.Feasible G →
          frobNorm (G - ratToReal G₀) ≤ 2 * ((C.n : ℝ) + 1 + C.M)) := by sorry

end STOC2027BoolCSP.Approximation
