-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_fixedTest_toCode
-- name    : QAlgorithms.Papers.Independent.Support50.P20.fixedTest_toCode
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:34:45.875604+00:00
-- url     : https://prove2.me/theorems/aeae426c-48d0-4e79-b6b5-e286a5ac6d06
-- title:
--   A fixed binary test yields an actual random-coding error bound
-- statement:
--   Let $W:x\mapsto\rho_x$ be any channel from a nonempty classical set $X$ to normalized trace-class states on $B$, and let $P$ be a discrete probability distribution on $X$. Form $\pi^{AB}=\sum_xP(x)|x\rangle\langle x|\otimes\rho_x$ and its marginals. Fix an effect $0\le Q\le I$ with $\operatorname{Tr}(Q\pi^{AB})\ge1-\epsilon'$, where $0\le\epsilon'<1$. For every $c>0$ and integer $m\ge1$, there is an actual $m$-message code with a complete decoding POVM and average error $e$ satisfying
--
--   $$
--   e\le(1+c)\epsilon'+(2+c+c^{-1})m\,\operatorname{Tr}\bigl(Q(\pi^A\otimes\pi^B)\bigr).
--   $$
--
--   This provides the fixed-test coding interface underlying achievability. The right-hand side need not be below one, and no pre-existing good code or invertible measurement sum is assumed.
--
--   **Formalization Note** The test is represented by its diagonal blocks $Q_x$; the two traces are respectively $\sum_xP(x)\operatorname{Tr}(Q_x\rho_x)$ and $\sum_{x,y}P(x)P(y)\operatorname{Tr}(Q_x\rho_y)$. Every effect has these blocks, and every family of effects has a bounded direct-sum realization.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 3, Unnumbered fixed-test random-coding bound, (8)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.3–4, (8): fixed-test random coding produces an actual complete
m-outcome decoding POVM. The left side is its resulting average error. The cq
test is represented exactly by its diagonal blocks, which are all the proof uses.
Completion on the square-root measurement's kernel is allowed. -/
theorem fixedTest_toCode {X I : Type*} [Nonempty X]
    (b : HilbertBasis I ℂ H) (W : ClassicalInputChannel X b) (P : PMF X)
    (Q : X → Effect H) (epsilonPrime c : ℝ)
    (hZero : 0 ≤ epsilonPrime) (hOne : epsilonPrime < 1) (hc : 0 < c)
    (hAccept : 1 - epsilonPrime ≤ cqJointAcceptance b W P Q)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ClassicalMessageCode X H m, uniformDecodingError b W C ≤
      (1 + c) * epsilonPrime + (2 + c + c⁻¹) * m * cqProductAcceptance b W P Q := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
