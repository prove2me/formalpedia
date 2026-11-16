-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_Supplement_theorem_3_4
-- name    : SFMQueryLower.EmptyMin.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:33.512433+00:00
-- url     : https://prove2.me/theorems/6aa3580c-4e34-4f86-ad53-bfb4e2eb08ee
-- title:
--   Theorem 3.4 — a deterministic algorithm recovers the layered partition with $O(n\log n)$ queries
-- statement:
--   Let $n\ge2$. For a partition $\Pi=(P_1,R_1,\dots,P_k,R_k)$ of $[n]$ into nonempty blocks (any $k$, any block sizes) and a bit $b\in\{0,1\}$, let $f_b^\Pi:2^{[n]}\to\mathbb R$ be the layered function of Definition 2.2.
--
--   There is an absolute constant $C>0$ such that for every $n\ge2$ there is a deterministic value-oracle algorithm $B_n$, depending only on $n$, with the following property. For every $k$, every partition $\Pi$ of $[n]$ into $2k$ blocks and every $b$, the algorithm run on $f_b^\Pi$ returns $\Pi$ (including $k$) after at most
--   $$C\,n\log n$$
--   value queries. Moreover, there is a map $m_n$ from partitions to subsets of $[n]$ such that $m_n(\Pi)$ is a minimizer of $f_b^\Pi$ for every $\Pi$ and $b$; so once $\Pi$ is recovered, a minimizer is returned without further queries.
--
--   The result shows that the $\Omega(n\log n)$ lower bounds for the layered family are tight for this family.
--
--   **Formalization Note** The ground set is `Fin n`; $\Pi$ is the published `OrderedPartition n k`, and the output type is the dependent pair `Σ k, OrderedPartition n k`. The query count counts every issued query, repeats included, and is in $[0,\infty]$; `Returns` requires halting.
--
--   Differences from the source:
--   - encoding: $O(n\log n)$ queries → one absolute constant $C$ with at most $C n\log n$ queries for every $n\ge2$; reason: for each fixed $n$ the deterministic algorithm's worst case over the finitely many inputs is finite and $\log n>0$, so an eventual bound and a bound for all $n\ge2$ are equivalent.
--   - encoding: "recovers $\Pi$" → returns the pair $\langle k,\Pi\rangle$; reason: $k$ is unknown to the algorithm, and an ordered partition is the pair.
--   - encoding: "can then return a minimizer without further queries" → a query-free map $m_n$ from recovered partitions to minimizers; reason: this is exactly computing a minimizer from $\Pi$ alone.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Theorem 3.4, printed p. 11 / PDF p. 12 (restated and proved in Appendix B.2, printed pp. 18–19 / PDF pp. 19–20)

import Definitions.Def_SFMQueryLower_EmptyMin_OracleStrategy
import Definitions.Def_SFMQueryLower_EmptyMin_HardFamily

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin.Supplement

/-- Fox, Theorem 3.4, printed p. 11 / PDF p. 12 (restated and proved in Appendix B.2,
printed pp. 18–19 / PDF pp. 19–20). The constant `C` precedes `n`; the deterministic strategy
`B` and the post-processing map `m` are chosen from `n` alone, before the number of layers `k`,
the partition `π` (any block sizes) and the bit `b`. `B` returns exactly `⟨k, π⟩` and issues
at most `C n log n` queries (worst case, repeated queries counted). The map `m` turns the
recovered partition into a minimizer of the queried function without further queries. -/
theorem theorem_3_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ B : OracleStrategy (Finset (Fin n)) ℝ (Σ k : ℕ, OrderedPartition n k),
      ∃ m : (Σ k : ℕ, OrderedPartition n k) → Finset (Fin n),
        ∀ (k : ℕ) (π : OrderedPartition n k) (b : Bool),
          Returns B (hardFunction π b) ⟨k, π⟩ ∧
          queryCount B (hardFunction π b) (fun _ => True) ≤
            ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ)) ∧
          ∀ S : Finset (Fin n), hardFunction π b (m ⟨k, π⟩) ≤ hardFunction π b S := by sorry

end SFMQueryLower.EmptyMin.Supplement
