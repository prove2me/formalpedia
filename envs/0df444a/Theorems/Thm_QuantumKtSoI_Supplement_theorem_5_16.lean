-- Prove2me | Theorems.Thm_QuantumKtSoI_Supplement_theorem_5_16
-- name    : QuantumKtSoI.Supplement.theorem_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:42:10.9098+00:00
-- url     : https://prove2.me/theorems/d149262a-7bdc-4891-a206-4c1c6956f9a1
-- title:
--   Theorem 5.16, p.65 — for every $C\ge1$ a quantum polynomial-time sampler violates symmetry with error $C\log$ with probability above $1/(8000n^2)$
-- statement:
--   For every constant $C\ge1$ there are a positive integer $\beta$, depending only on $C$, and a quantum polynomial-time sampler $S$ such that:
--
--   1. for infinitely many $n$, with probability greater than $1/(8000n^2)$ the output of $S(1^n)$ is a pair $\langle x,y\rangle$ of strings of length $n$ with
--   $$\mathrm{qKt}(y|x)>\mathrm{qKt}(\langle x,y\rangle)-\mathrm{qKt}(x)+C\log(|x|+|y|+2);$$
--   2. every output of $S(1^n)$ is either $\langle0^n,0^n\rangle$ or $\langle\mathrm{pad}_n(P),\mathrm{pad}_n(b)\rangle$ for strings $P,b$ with $|P|,|b|<n$ and $|b|\le\beta\lceil\log(n+2)\rceil$, where $\mathrm{pad}_n(v)=v10^{n-|v|-1}$.
--
--   So symmetry of information for $\mathrm{qKt}$ does not hold on average with error $C\log$, with the same polynomial $p(n)=8000n^2$ for every $C$.
--
--   A quantum polynomial-time sampler is a machine with a polynomial all-branch deadline on $1^n$; an output that is not a pair of $n$-bit strings is outside the event.
--
--   **Formalization Note** "Every output" is every string of positive output probability at the deadline.
--
--   Differences from the source:
--   - generalization: the glue routines are fixed once and for all by their p.24 properties → every admissible glue routine set G (hypothesis G.Admissible); descriptions, P_e and qKt are those of G; reason: the proofs use only the p.24 properties and the paper's routines are one admissible set; same as the published base items
--   - encoding: a quantum polynomial-time sampler: a machine S and a polynomial q_S → a valid coded machine with all-branch deadline c(n+2)^k on 1ⁿ (QSampler); reason: every polynomial is bounded by one of this form and the output law does not change after all branches have halted
--   - encoding: "a polynomial p positive for all large n … One may take p(n) = 8000n² for every C" → stated with p(n) = 8000n²; reason: the paper's own strongest form; it implies the existence of p
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem 5.16, p.65; samplers and Definition 5.1, p.51; pad, p.60

import Mathlib
import Definitions.Def_QuantumKtSoI_qKt
import Definitions.Def_QuantumKtSoI_Supplement_QSampler

open Classical

namespace QuantumKtSoI.Supplement

/-- **Theorem 5.16** (Failure of symmetry of information on average; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…, p.65). For every
constant `C ≥ 1`, symmetry of information for qKt does not hold on average with error `C log`: there
are a quantum polynomial-time sampler `S` and the polynomial `p(n) = 8000n²` (the same for every
`C`) such that, for infinitely many `n`, with probability greater than `1/p(n)` the output of
`S(1ⁿ)` is a pair `⟨x, y⟩` of strings of length `n` with
`qKt(y|x) > qKt(⟨x,y⟩) − qKt(x) + C log(|x|+|y|+2)`. Moreover `S` is chosen together with a positive
integer `β` depending only on `C` so that every output of `S(1ⁿ)` is either `⟨0ⁿ, 0ⁿ⟩` or
`⟨pad_n(P), pad_n(b)⟩` for strings `P, b` with `|P|, |b| < n` and `|b| ≤ β⌈log(n+2)⌉`.

**Formalization Note** `G` is any admissible glue routine set (p.24). The sampler is a `QSampler`
(valid coded machine with an all-branch deadline `c(n+2)^k` on `1ⁿ`, p.51); `S.pairProb` is the
probability that the output is `⟨x,y⟩ = xy` with `x, y ∈ {0,1}ⁿ` and the event; "every output" is
every `w` with `P_S(1ⁿ; q_S(n), w) > 0`. Quantifier order: `∀ C, ∃ β, ∃ S`. -/
theorem theorem_5_16 (G : GlueRoutines) (hG : G.Admissible) :
    ∀ C : ℝ, 1 ≤ C → ∃ β : ℕ, 0 < β ∧ ∃ S : QSampler,
      (∀ N : ℕ, ∃ n ≥ N, 1 / (8000 * (n : ℝ) ^ 2) <
        S.pairProb n fun x y =>
          (qKt G (pair x y) [] : ℝ) - qKt G x [] + C * Real.logb 2 ((x.length : ℝ) + y.length + 2) <
            qKt G y x) ∧
      ∀ n : ℕ, ∀ w : List Bool, 0 < S.outProb n w →
        w = pair (List.replicate n false) (List.replicate n false) ∨
          ∃ P b : List Bool, P.length < n ∧ b.length < n ∧ b.length ≤ β * Nat.clog 2 (n + 2) ∧
            w = pair (pad n P) (pad n b) := by sorry

end QuantumKtSoI.Supplement
