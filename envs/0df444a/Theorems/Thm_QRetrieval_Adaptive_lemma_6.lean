-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_lemma_6
-- name    : QRetrieval.Adaptive.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:09.424198+00:00
-- url     : https://prove2.me/theorems/c1b25532-a8fa-4bc2-8179-9db64bb6f7d2
-- title:
--   Lemma 6 — the adaptive two-probe scheme: $|M_1|=O(m_1\log(m_1/n))$, $|M_2|=2n\lceil m/m_1\rceil$, one quantum probe into $M_1$ locates the bit in $M_2$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge1$ and $m_1$ satisfy $2n\le m_1$ and $2m_1\le m$. Then there are a length $a\le C\, m_1\log_2(m_1/n)$ and
--
--   1. storage maps $M_1:B(m,n)\to\{0,1\}^a$ and $M_2:B(m,n)\to\{0,1\}^{2n\lceil m/m_1\rceil}$;
--   2. for each index $i\in[m]$, a quantum algorithm $A_i$ making **exactly one** query to the oracle $O_{M_1(x)}$ (on a work register fixed in advance), together with a map $\mathrm{loc}_i$ from measurement outcomes to $\{\bot\}\cup[2n\lceil m/m_1\rceil]$; neither $A_i$ nor $\mathrm{loc}_i$ depends on $x$;
--
--   such that
--
--   1. $\mathrm{wt}_H(M_2(x))\le n$ for every $x\in B(m,n)$;
--   2. for every $x\in B(m,n)$ and every $i\in[m]$ there is an address $p$ such that the measured outcome of $A_i$ yields $p$ with probability $1$, and
--   $$
--   x_i=\begin{cases}M_2(x)_p,& p\neq\bot,\\ 0,& p=\bot.\end{cases}
--   $$
--
--   In words: $x$ is compressed into $M_1\circ M_2$, and any bit of $x$ is retrieved by one quantum probe into $M_1$ followed by one classical probe into $M_2$. In the paper's construction $x$ is cut into $m_1$ blocks, the non-zero blocks are matched into $2n$ slots of $M_2$ with the graph of Lemma 3, and $M_1$ stores for each block the Hadamard encoding of its matching label, which one Bernstein–Vazirani query reads exactly. Since $M_2$ again has weight at most $n$, the classical probe can itself be replaced by a scheme for $M_2$ (Eq. (3)).
--
--   **Formalization Note** The quantum probe is a `QAlgorithms.QueryAlg (Fin a) Bool W 1` run with `controlledPhaseOracle (M₁ x)`; the address is `loc i` applied to the computational-basis outcome, an `Option` whose `none` is the paper's label $0$ ("the query returns 0").
--
--   Differences from the source:
--   - generalization: a valid two-probe scheme into M1 ◦ M2 whose query algorithm makes one quantum probe into M1 followed by a classical probe into M2 → locator form: a 1-query algorithm on M1's oracle whose measured outcome gives one address p with probability 1, and x_i = M2(x)_p (0 if p = none); reason: a locator gives the paper's two-probe scheme (probe M1, then read M2 at p); it also fixes the address deterministically, as the paper's construction does
--   - generalization: |M2| = 2n(m/m1), with m1 dividing m implicit ("m1 equal substrings of m/m1 bits") → |M2| = 2n⌈m/m1⌉ for every m1; reason: equals 2n(m/m1) when m1 divides m
--   - generalization: (no weight clause in Lemma 6) → additionally wt_H(M2(x)) ≤ n for every x; reason: the property §4 (p. 10) uses to recurse on M2; true for the construction, which copies the non-zero blocks of x
--   - encoding: |M1| = O(m1 log(m1/n)) (O(·), log of unspecified base) → ∃ C : ℝ chosen before every variable; log = Real.logb 2; reason: an absolute constant is what O(·) means here; the base of the logarithm only changes C
--   - encoding: Fix m1 such that 2n ≤ m1 ≤ m/2 → 1 ≤ n, 2 * n ≤ m₁, 2 * m₁ ≤ m; reason: log(m1/n) is undefined at n = 0; m1 ≤ m/2 is 2m1 ≤ m without division
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Lemma 6, p. 8 (construction pp. 7–8)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QRetrieval_Adaptive_B

namespace QRetrieval.Adaptive

/-- **Lemma 6 (the adaptive two-probe scheme: one quantum probe into `M1`, one classical probe
into `M2`).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Lemma 6, p. 8: "Fix `m1` such that `2n ≤ m1 ≤ m/2`. There is a valid adaptive
two-probe compression scheme that compresses a string `x ∈ {0,1}^m` into a string of the form
`M1 ◦ M2`, where `|M1| = O(m1 log(m1/n))` and `|M2| = 2n(m/m1)`. The query algorithm can retrieve
any bit of `x` by making one quantum probe into `M1` followed by a classical probe into `M2`."

There is an absolute constant `C` such that for all `n ≥ 1` and `m1` with `2n ≤ m1` and
`2 m1 ≤ m` there exist a length `a ≤ C · m1 · log₂(m1/n)`, storage maps
`M₁ : B(m, n) → {0,1}^a` and `M₂ : B(m, n) → {0,1}^{2n⌈m/m1⌉}`, and, for each index `i`, a
one-query algorithm `A i` on the oracle of `M₁` with an output map `loc i` into
`{none} ∪ [2n⌈m/m1⌉]`, such that
1. `M₂(x)` has Hamming weight at most `n` for every `x`;
2. for every `x ∈ B(m, n)` and every `i`, the measured outcome of `A i` run with oracle
   `O_{M₁(x)}` equals one fixed address `p` with probability `1`, and `x_i = M₂(x)_p`
   (`x_i = 0` when `p = none`).

The construction of pp. 7–8: cut `x` into `m1` blocks of `⌈m/m1⌉` bits; take `G` from Lemma 3 with
`k = m1` and a matching `(ℓ_u)` of the non-zero blocks (Remark after Lemma 3); store in `M1[u]` the
Hadamard codeword `h(ℓ_u)` (`h(0)` for zero blocks) and in `M2[G(u, ℓ_u)]` the block `b_u`;
retrieve `ℓ_u` with one Bernstein–Vazirani query.

**Formalization Note.** The clauses "compresses into `M1 ◦ M2`" and "one quantum probe into `M1`
followed by a classical probe into `M2`" are stated in locator form: `M₁` and `M₂` are given
separately; the quantum probe is a `QAlgorithms.QueryAlg` with exactly one query to the phase
oracle `O_{M₁(x)}`, fixed independently of `x`; its measured outcome (computational basis, then
`loc i`) is the address `p` of the classical probe, with probability `1`. `p = none` is the
paper's "if `j` is 0 then the query returns 0". The block length is `⌈m/m1⌉` (the paper assumes
`m1 ∣ m` and writes `m/m1`); the weight clause 1 is not printed in Lemma 6 but is the property
§4 (p. 10) uses ("a memory that is always assigned a string of Hamming weight at most `n`").
`O(·)` is an absolute `C` before all variables, `log = log₂`, and `n ≥ 1` (`log(m1/n)`). -/
theorem lemma_6 : ∃ C : ℝ, ∀ m n m₁ : ℕ, 1 ≤ n → 2 * n ≤ m₁ → 2 * m₁ ≤ m →
    ∃ a : ℕ, (a : ℝ) ≤ C * m₁ * Real.logb 2 ((m₁ : ℝ) / n) ∧
    ∃ (M₁ : B m n → Fin a → Bool) (M₂ : B m n → Fin (2 * n * ⌈(m : ℝ) / m₁⌉₊) → Bool)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : Fin m → QAlgorithms.QueryAlg (Fin a) Bool W 1)
      (loc : Fin m → (Fin a × Bool) × W → Option (Fin (2 * n * ⌈(m : ℝ) / m₁⌉₊))),
      (∀ x, QAlgorithms.hammingWeight (M₂ x) ≤ n) ∧
      ∀ x i, ∃ p, (A i).outputProb (QAlgorithms.controlledPhaseOracle (M₁ x)) (loc i) p = 1 ∧
        x.1 i = p.elim false (M₂ x) := by sorry

end QRetrieval.Adaptive
