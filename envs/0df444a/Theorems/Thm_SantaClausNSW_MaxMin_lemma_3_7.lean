-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_7
-- name    : SantaClausNSW.MaxMin.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:10.551197+00:00
-- url     : https://prove2.me/theorems/586b0ed3-e7f1-4cd2-8797-927f3a0a1a32
-- title:
--   Lemma 3.7 — f-scaled prices give an additive lower bound with positive baseline µ satisfying (15)
-- statement:
--   Let $v$ be a normalized, monotone, subadditive valuation with $v(S)=W>0$, let $\nu=\max_{j\in S}v(\{j\})$, and let $0<f_j\le1$ for $j\in S$. Put $P=\sum_{j\in S}(1-f_j)/f_j$ and $s=|S|$. Using polynomially many restricted demand queries one can find an additive lower bound $a\in[0,\nu]^S$ ($a(Q)\le v(Q)$ for $Q\subseteq S$) whose baseline $\mu=\sum_{j\in S}f_ja_j$ is positive and satisfies
--   $$\frac{3W}{4}\le\mu\Big[2+\log_2\frac{s\nu}{\mu}\Big]+4\sqrt{\nu P\mu}.\tag{15}$$
--   This replaces supporting clauses for subadditive valuations in Corollary 3.8.
--
--   Differences from the source:
--   - encoding: 'using polynomially many restricted demand queries, we can find' → a program on the mission's RAM that, with any correct restricted demand oracle, halts on every run after at most c·(1 + size)^d restricted demand queries, c, d fixed before the input; no running-time claim; reason: the lemma claims a polynomial query count only (p. 22: polynomial in the encodings of the values and weights)
--   - reading: running time polynomial in the encoding of the valuation values (§2, p. 10) → valuation values are a/b with naturals a, b ≤ 2^σ, b ≠ 0, and σ is part of the input (size n + m + σ); reason: App. E.1 (p. 67) makes the §2 convention concrete with the known bound σ
--   - encoding: one valuation v and its restricted demand queries → the one-agent family (fun _ : Fin 1 => v); questions carry agent index 0; reason: the oracle predicates are stated for families; one agent is the single valuation
--   - encoding: weights 0 < f_j ≤ 1 → rational f_j, given in the input with 1_S; reason: the program needs them as data; the proof's prices t_ℓ/f_j are rational
--   - encoding: ν = max_{j∈S} v({j}) → maxItemValue v S of the published definition (the maximum over the nonempty S); reason: S ≠ ∅ since v(S) > 0 = v(∅)
--   - encoding: log₂ → Real.logb 2; reason: same function on positive arguments; sν/µ > 0
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 20, Lemma 3.7

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

open MultiAllocToAlloc.Subadditive

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.7** (p. 20). There are a program and constants `c, d` such that, for every
normalized monotone subadditive valuation `v` with values `a/b`, `a, b ≤ 2^σ`, every set `S`
with `W = v(S) > 0`, every rational weights `0 < f_j ≤ 1` (`j ∈ S`) and every correct
restricted demand oracle, every run halts after polynomially many (at most
`c (1 + size)^d`) restricted demand queries and outputs an additive lower bound `a ∈ [0, ν]^S`
(`ν = max_{j ∈ S} v({j})`) whose baseline `µ = ∑_{j ∈ S} f_j a_j` is positive and satisfies
`3W/4 ≤ µ [2 + log₂(sν/µ)] + 4 √(νPµ)`, where `P = ∑_{j ∈ S} (1 − f_j)/f_j` and `s = |S|`. -/
theorem lemma_3_7 :
    ∃ (P : Program) (c d : ℕ), ∀ (m σ : ℕ) (v : Finset (Fin m) → ℝ),
      IsValuation v → IsSubadditive v → BitBounded (fun _ : Fin 1 => v) σ →
      ∀ S : Finset (Fin m), 0 < v S →
      ∀ f : Fin m → ℚ, (∀ j ∈ S, 0 < f j ∧ f j ≤ 1) →
      ∀ O : Oracle, IsRestrictedDemandOracle (fun _ : Fin 1 => v) O →
        ∃ K : ℕ, ∀ s ∈ (run P O K (initState ([(m : ℚ), (σ : ℚ)] ++ encSet S ++
            List.ofFn (fun j => if j ∈ S then f j else 0)))).support,
          s.halted = true ∧
          s.queries ≤ c * (1 + σ + explicitSize 1 m ([(m : ℚ), (σ : ℚ)] ++ encSet S ++
            List.ofFn (fun j => if j ∈ S then f j else 0))) ^ d ∧
          (∀ j ∈ S, 0 ≤ ((outList s.mem).getD (j : ℕ) 0 : ℝ) ∧
            ((outList s.mem).getD (j : ℕ) 0 : ℝ) ≤ maxItemValue v S) ∧
          IsAdditiveLowerBound v S (fun j => ((outList s.mem).getD (j : ℕ) 0 : ℝ)) ∧
          0 < ∑ j ∈ S, (f j : ℝ) * ((outList s.mem).getD (j : ℕ) 0 : ℝ) ∧
          3 * v S / 4 ≤
            (∑ j ∈ S, (f j : ℝ) * ((outList s.mem).getD (j : ℕ) 0 : ℝ)) *
              (2 + Real.logb 2 ((S.card : ℝ) * maxItemValue v S /
                ∑ j ∈ S, (f j : ℝ) * ((outList s.mem).getD (j : ℕ) 0 : ℝ))) +
            4 * Real.sqrt (maxItemValue v S * (∑ j ∈ S, (1 - (f j : ℝ)) / (f j : ℝ)) *
              ∑ j ∈ S, (f j : ℝ) * ((outList s.mem).getD (j : ℕ) 0 : ℝ)) := by sorry

end SantaClausNSW.MaxMin
