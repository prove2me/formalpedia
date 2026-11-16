-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_Supplement_theorem_8_1
-- name    : STOC2027BoolCSP.Approximation.Supplement.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:02.156585+00:00
-- url     : https://prove2.me/theorems/fbc47dd0-70fd-420b-8d10-45c0253214b3
-- title:
--   Theorem 8.1 (= Theorem 1.2) — deterministic $(\alpha_k-\varepsilon)$-approximation for Boolean Max-$k$-CSP in time polynomial in the input length and $1/\varepsilon$
-- statement:
--   Fix an integer $k\ge5$ and write $\alpha_k=(k+1)/2^k$. There is a deterministic algorithm which, given an explicit Boolean Max-$k$-CSP instance $I$ with nonnegative rational weights and a rational $\varepsilon>0$, returns an exactly Boolean assignment $x\in\{-1,1\}^n$ of the $n$ variables of $I$ with
--   $$\mathrm{val}_I(x)\ \ge\ (\alpha_k-\varepsilon)\,\mathrm{OPT}(I).$$
--   Its running time is at most $P(L+\lceil1/\varepsilon\rceil)$, where $L$ is the bit length of the input $(I,\varepsilon)$ and $P$ is a polynomial depending only on $k$. $\mathrm{OPT}$ is the optimum of the original, unnormalized instance.
--
--   This is the derandomized counterpart of Theorem 1.1, the goal of the mission: it trades the $\log(1/\varepsilon)$ dependence for a $1/\varepsilon$ dependence and removes the random bits.
--
--   Differences from the source:
--   - encoding: deterministic algorithm with running time polynomial in the total input bit length and 1/ε, exponent depending on k → one CoinMachine run on the empty random tape, halting within P(1 + L + ⌈1/ε⌉) steps, L the length of requestCode I ε; reason: the live mission's machine model and request encoding; requestCode includes ε as the paper's input length does
--   - generalization: for every rational ε > 0 there is a deterministic algorithm → one machine and one polynomial serve every ε, which is part of the input; reason: fixing ε specializes it to the source's statement
--   - reading: Theorem 8.1: returns an assignment → an exactly Boolean output word of length n, decoded coordinatewise; reason: Theorem 1.2, the same result in the introduction, says exactly Boolean assignment
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 2 (PDF 5), Theorem 1.2, and printed p. 17 (PDF 20), Theorem 8.1, proof §§8.1–8.4 (printed 17–20)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine

namespace STOC2027BoolCSP.Approximation.Supplement

open STOC2027BoolCSP.Approximation

/-- Theorem 8.1 (deterministic implementation), printed p. 17; also Theorem 1.2, printed p. 2.
For every fixed `k ≥ 5` there are one finite bit machine and one polynomial `P` such that for
every Boolean Max-`k`-CSP instance `I` with nonnegative rational weights and every rational
`ε > 0`, the run on the request code of `(I, ε)` with the empty random tape (a deterministic
computation) halts within `P(1 + L + ⌈1/ε⌉)` steps, `L` the request bit length, with an exactly
Boolean assignment of the `n` variables whose value is at least `(α_k − ε) OPT(I)`. -/
theorem theorem_8_1 (k : ℕ) (hk : 5 ≤ k) :
    ∃ (Mach : CoinMachine) (P : Polynomial ℕ),
      ∀ (I : Instance) (ε : ℚ), I.IsMaxkCSP k → 0 < ε →
        ∃ out : List Bool,
          Mach.HaltsWithin (requestCode I ε) []
            (P.eval (1 + (requestCode I ε).length + ⌈1 / ε⌉₊)) out ∧
          out.length = I.n ∧
          (alpha k - ε) * I.opt ≤ I.val (decodeAssignment I.n out) := by sorry

end STOC2027BoolCSP.Approximation.Supplement
