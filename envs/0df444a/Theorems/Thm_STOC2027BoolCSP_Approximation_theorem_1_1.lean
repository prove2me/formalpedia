-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_theorem_1_1
-- name    : STOC2027BoolCSP.Approximation.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:54.913613+00:00
-- url     : https://prove2.me/theorems/3ee6ced0-09cb-4cd7-a1bf-25a6c2202e61
-- title:
--   Theorem 1.1 — finite-bit randomized $(\alpha_k-\varepsilon)$-approximation for Boolean Max-$k$-CSP
-- statement:
--   Write $\alpha_k=(k+1)/2^k$. For every fixed integer $k\ge5$ and every rational $\varepsilon>0$ there is a randomized algorithm for Boolean Max-$k$-CSP with nonnegative rational constraint weights that returns an exactly Boolean assignment $x$ satisfying
--   $$\mathbb E\,\mathrm{val}(x)\;\ge\;(\alpha_k-\varepsilon)\,\mathrm{OPT}.$$
--   The running time and the number of random bits are polynomial in the explicit input bit length and in the requested precision $\log(1/\varepsilon)$. The guarantee is in expectation over the algorithm's finite random bits.
--
--   Precisely, for each $k\ge5$ there are one finite randomized bit machine and polynomials $P,Q$ depending only on $k$ with the following property. Let $I$ be any Boolean Max-$k$-CSP instance with nonnegative rational weights, let $\varepsilon>0$ be rational, let $L$ be the length of the code of the request $(I,\varepsilon)$, and let $p=\max(0,\lceil\log_2(1/\varepsilon)\rceil)$. On the request and on every random tape of $R=P(1+L+p)$ unbiased bits, the machine halts within $Q(1+L+p)$ steps and outputs an $n$-bit assignment $x(s)$. Moreover
--   $$2^{-R}\sum_{s\in\{0,1\}^R}\mathrm{val}_I(x(s))\;\ge\;(\alpha_k-\varepsilon)\,\mathrm{OPT}(I).$$
--   Arbitrary incidence patterns, repeated variables, constant predicates, zero weights and zero optimum are all included.
--
--   For odd $k\ge5$ the ratio matches the Unique Games hardness bound of De and Mossel. It is the paper's first main result.
--
--   Differences from the source:
--
--   - encoding: a randomized algorithm with polynomial running time and random bits → one fixed CoinMachine (FinTM2, finite alphabets) run on a random tape of exactly P(1 + L + p) bits, halting within Q(1 + L + p) steps on every tape; reason: ordinary finite-bit randomized Turing computation; an algorithm using fewer random bits pads its tape, and a fixed polynomial tape length gives the machine no advice
--   - encoding: E val(x) over the finite random bits → the uniform average of val over all 2^R tapes; reason: the same expectation
--   - encoding: explicit input; assignment in {−1,1}^n → requestCode (unary variable list, self-delimiting binary numbers, reduced rationals, explicit truth tables, then ε); an n-bit output word, true ↦ +1; reason: standard explicit encodings; L is the length of the code
--   - reading: polynomial in the explicit input bit length and log(1/ε) → polynomial in 1 + L + p with L including the code of ε; reason: the preamble of Section 1.1: the input length includes the representation of the accuracy parameter
--   - generalization: the resource bounds are claimed when 0 < ε < 1 → the same polynomial bounds for every rational ε > 0 (with p = 0 for ε ≥ 1); reason: the bound is required on a larger set of accuracies; it specializes to the source's claim, and the paper's own remark (run with min{ε,1}) covers ε ≥ 1
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 1 (PDF 4), Theorem 1.1 (with equation (1) and the preamble of Section 1.1)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine

namespace STOC2027BoolCSP.Approximation

/-- Theorem 1.1 (approximation algorithm), printed p. 1. For every fixed `k ≥ 5` there are one
finite randomized bit machine and polynomials `P` (random bits) and `Q` (steps) such that for every
Boolean Max-`k`-CSP instance `I` with nonnegative rational weights and every rational `ε > 0`,
writing `L` for the request bit length and `p = max(0, ⌈log₂(1/ε)⌉)`, the machine run on the
request and any tape of `R = P(1 + L + p)` unbiased bits halts within `Q(1 + L + p)` steps with an
exactly Boolean assignment of the `n` variables, and the average of `val_I` over all `2^R` tapes is
at least `(α_k − ε) OPT(I)`. -/
theorem theorem_1_1 (k : ℕ) (hk : 5 ≤ k) :
    ∃ (Mach : CoinMachine) (P Q : Polynomial ℕ),
      ∀ (I : Instance) (ε : ℚ), I.IsMaxkCSP k → 0 < ε →
        ∃ out : (Fin (P.eval (1 + (requestCode I ε).length + precBits ε)) → Bool) → List Bool,
          (∀ s, Mach.HaltsWithin (requestCode I ε) (List.ofFn s)
              (Q.eval (1 + (requestCode I ε).length + precBits ε)) (out s) ∧
            (out s).length = I.n) ∧
          (alpha k - ε) * I.opt ≤
            (∑ s, I.val (decodeAssignment I.n (out s))) /
              2 ^ (P.eval (1 + (requestCode I ε).length + precBits ε)) := by sorry

end STOC2027BoolCSP.Approximation
