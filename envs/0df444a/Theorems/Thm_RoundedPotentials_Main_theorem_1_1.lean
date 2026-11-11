-- Prove2me | Theorems.Thm_RoundedPotentials_Main_theorem_1_1
-- name    : RoundedPotentials.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T08:35:24.866964+00:00
-- url     : https://prove2.me/theorems/1bfd6db6-1421-4f4d-b4ad-be8a80c5af45
-- title:
--   Theorem 1.1 — exact maximum-flow certificates, size, correctness, cost and words
-- statement:
--   Let $s\ne t$ be vertices of a directed graph on $n$ vertices with an edge list of length $m$, without loops or repeated ordered pairs. Capacities are nonnegative integers at most $W\ge1$. The verifier is the concrete instrumented p.17 procedure, with denominator $Q_0=32n^2W$ and integer tolerance $4nW=Q_0/(8n)$.
--
--   It satisfies all four assertions:
--
--   1. Every accepted list has exactly $n$ integer entries. Each entry lies in $[0,(2n-1)Q_0]$ and has at most $3\lfloor\log_2(nW)\rfloor+10$ binary digits.
--   2. For every integer $p\ge0$,
--   $$\bigl(\exists\text{ certificate accepted by the verifier for }p\bigr)\iff\operatorname{MaxFlow}(s,t)=p.$$
--   3. For every integer claim and every certificate list, including negative, oversized, too short and too long inputs, the number of counted operations is at most $100(n+m)+100$.
--   4. Every recorded operand and result has magnitude at most $64n^3W^2$ and binary length at most $3\lfloor\log_2(nW)\rfloor+10$.
--
--   These universal numerals instantiate both asymptotic bounds. The word-size statistic exempts only the untrusted operands of the initial raw input-range comparisons; those comparisons remain counted. All later arithmetic is recorded by primitives. The verifier reads neither a supplied flow nor a supplied cut and never queries maximum flow. This states the exact result certified by rounded potentials together with the verifier's size and computation guarantees.
--
--   Differences from the source:
--   - encoding: a finite vertex set V of size n → vertices Fin n and an edge list with distinct loopless ordered pairs; reason: relabeling preserves every flow and cut; m is the actual list length; zero capacities are explicitly allowed in §3
--   - encoding: MaxFlow(s,t) = p → IsGreatest of the set of real values of published IsFlow assignments; reason: records attainment without a real supremum default; the published definition has the same signed conservation equations
--   - reading: O(log(nW)) bits per potential → binaryDigits ≤ 3 * Nat.log 2 (n * W) + 10 for every accepted index; reason: (2n−1)Q₀ < 64(nW)³; the numerals 3 and 10 are fixed uniformly before the instance
--   - reading: O(n+m) arithmetic operations → at most 100(n+m)+100 primitive operations for every integer claim and certificate list of any length; reason: the p.17 loops have bounded parsing, two interval tests per vertex, six operations per edge, seven final operations per vertex, and constant setup; 100 is a uniform slack bound
--   - reading: operations on O(log(nW))-bit integers → recorded operands/results have magnitude at most 64n³W² and at most 3 * Nat.log 2 (n * W) + 10 bits; reason: partial counters and targets are bounded by (n−1)Q₀W; a final difference doubles this; the polynomial is at most 64(nW)³
--   - encoding: reject malformed or oversized fields → typed integer lists with bounded length/range parsing; raw claim/index range comparisons are counted but their untrusted operands are exempt from the word-size statistic; reason: a rejected arbitrary integer cannot have a universal word-size bound; all later operands/results and all guard bounds/results are recorded; structural RAM bookkeeping and instrumentation are outside integer arithmetic
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 3, Theorem 1.1; p.17, Proof of Theorem 1.1

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Verifier

namespace RoundedPotentials.Main
open scoped BigOperators

theorem theorem_1_1 {n W : ℕ} (I : Instance n W) (hW : 1 ≤ W)
    (s t : Fin n) (hst : s ≠ t) :
    (∀ (p : ℤ) (certificate : List ℤ), (verify I s t p certificate).1 = true →
      certificate.length = n ∧ ∀ i ∈ certificate,
        0 ≤ i ∧ i ≤ (2 * (n : ℤ) - 1) * (denominator n W : ℤ) ∧
        binaryDigits i ≤ 3 * Nat.log 2 (n * W) + 10) ∧
    (∀ p : ℤ, 0 ≤ p →
      ((∃ certificate : List ℤ, (verify I s t p certificate).1 = true) ↔
        MaxValue I s t (p : ℝ))) ∧
    (∀ (p : ℤ) (certificate : List ℤ),
      (verify I s t p certificate).2.ops ≤ 100 * (n + I.edges.length) + 100) ∧
    (∀ (p : ℤ) (certificate : List ℤ),
      (verify I s t p certificate).2.maxAbs ≤ 64 * n ^ 3 * W ^ 2 ∧
      Nat.log 2 ((verify I s t p certificate).2.maxAbs) + 1 ≤
        3 * Nat.log 2 (n * W) + 10) := by sorry

end RoundedPotentials.Main
