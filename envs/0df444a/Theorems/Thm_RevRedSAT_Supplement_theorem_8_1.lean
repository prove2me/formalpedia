-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_8_1
-- name    : RevRedSAT.Supplement.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:02:34.179455+00:00
-- url     : https://prove2.me/theorems/4265020a-b759-417d-a9b5-8bf609b2d0fb
-- title:
--   Theorem 8.1 — counting set covers of size at most $b$ in $2^{O(t\eta(t)^2/\sqrt{\lambda(t)})}$, $t=p+q$
-- statement:
--   Assume the Counting $d$-SAT Assumption 4.5. Let $U$ be a universe of $p$ elements, $S_1,\dots,S_q\subseteq U$ an explicitly given indexed family, $t=p+q$ and $b$ an integer. There are a deterministic algorithm and a constant $C$ that output
--
--   $$\#\Bigl\{X\subseteq[q] : |X|\le b,\ \textstyle\bigcup_{i\in X}S_i=U\Bigr\}$$
--
--   within
--
--   $$\Bigl\lfloor 2^{C\,t\eta(t)^2/\sqrt{\lambda(t)}}+C\,|w|\Bigr\rfloor$$
--
--   steps on every code $w$ of the instance.
--
--   The count is the paper's tool for exact counting of dominating sets (Corollary 8.2) and, through a cardinality-preserving bijection, of hitting sets.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - reading: time 2^{O(tη(t)²/√λ(t))}, with a budget given in binary and unbounded → ⌊2^{C·tη(t)²/√λ(t)} + C·|w|⌋ steps; reason: a Mathlib TM2 machine halts only with every non-output stack empty, so it spends steps linear in |w|, and an arbitrary binary budget makes |w| larger than any function of the measure; the extra term only pays for reading the input and is absorbed by the exponential whenever the budget is at most exponential in the measure
--   - encoding: the number is computed → the number is output in self-delimiting binary (encNat); reason: a fixed code of the output
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.1, p.56 (printed) = PDF p.58; App. C.1, p.92

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_lam
import Definitions.Def_RevRedSAT_Supplement_CountingDSAT
import Definitions.Def_RevRedSAT_Supplement_SCInstance

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **Theorem 8.1 (counting bounded set covers).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 8.1, p.56: "Assume the Counting d-SAT Assumption. Let U be a universe of p elements and
S1, . . . , Sq ⊆ U an explicitly given indexed family. Let t = p + q. For any integer budget b, the
number of index sets X ⊆ [q] satisfying |X| ≤ b and ⋃_{i∈X} Si = U can be computed
deterministically in time 2^{O(tη(t)²/√λ(t))}."

Under Assumption 4.5 there are a machine with finite alphabets and a constant `C` such that on every
code `w` of every instance `(p, S_0, …, S_{q−1}, b)`, with `t = p + q`, the machine outputs the
number of covering index sets of size at most `b` (`coverCount`, in self-delimiting binary) within
`⌊2^{C·tη(t)²/√λ(t)} + C·|w|⌋` steps.

**Formalization Note** Mathlib's TM2 halts only with every non-output stack empty, so every machine
spends a number of steps linear in `|w|`; the budget `b` is an arbitrary integer in binary, so `|w|`
is not bounded by any function of `t`. The additive `C·|w|` pays for this; for `|b| ≤ 2^{t}` it is
absorbed by the exponential term. -/
theorem theorem_8_1 :
    CountingDSAT →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ C : ℝ,
        ∀ (I : SCInstance) (w : List Bool), IsSCCode I w →
          HMBinPacking.OutputsWithin M w (encNat (coverCount I))
            ⌊(2 : ℝ) ^ (C * ((I.p + I.q : ℕ) : ℝ) * eta (I.p + I.q) ^ 2 /
                Real.sqrt (lam (I.p + I.q))) + C * w.length⌋₊ := by sorry

end RevRedSAT.Supplement
