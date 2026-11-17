-- Prove2me | Theorems.Thm_PathCount2k_Supplement_theorem_1_2
-- name    : PathCount2k.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:22:14.736352+00:00
-- url     : https://prove2.me/theorems/92a3b875-44d8-4ba1-bc16-3aafa5df64e7
-- title:
--   Theorem 1.2 — trees, forests, their orientations and treewidth-$t$ patterns counted to $1\pm\varepsilon$ in $(2+\eta)^k n^{O(\eta^{-1}\log(2/\eta))}\varepsilon^{-2}\log(2/\delta)$ operations
-- statement:
--   Fix $0<\eta\le1$. Let $c$ be the least integer $c\ge2$ with $(ec)^{1/c}\le 1+\eta/2$ (so $c=O(\eta^{-1}\log(2/\eta))$). The algorithm of §3 receives a pattern $H$ on $k$ vertices, a host graph $G$ on $n$ vertices, and $0<\varepsilon,\delta<1$, and returns an estimate $\widehat N$ of the number $N$ of embeddings of $H$ into $G$ (injective maps preserving every edge, or every arc in its direction). There is an absolute constant $a$ such that for every such $\eta$:
--
--   1. **Trees and forests.** There is a constant $C_\eta$ such that for every forest $H$ (in particular every tree) and every undirected graph $G$, and also for every orientation of a forest $H$ and every directed graph $G$,
--   $$
--   \Pr\big[|\widehat N-N|\le\varepsilon N\big]\ge1-\delta,
--   $$
--   and every run uses at most
--   $$
--   C_\eta\,(2+\eta)^k\,(n+1)^{a\,\eta^{-1}\log(2/\eta)}\,\varepsilon^{-2}\log(2/\delta)
--   $$
--   arithmetic operations.
--   2. **Bounded treewidth.** For every $t$ there is a constant $C_{\eta,t}$ such that for every undirected pattern $H$ of treewidth at most $t$ and every undirected $G$ the same accuracy guarantee holds, and every run uses at most
--   $$
--   C_{\eta,t}\,(2+\eta)^k\,(n+1)^{a\,\eta^{-1}\log(2/\eta)}\,(n+1)^{a\,\eta^{-1}\log(2/\eta)\,(t+1)}\,\varepsilon^{-2}\log(2/\delta)
--   $$
--   arithmetic operations.
--
--   The probability is over the algorithm's fair random bits. Compared with Theorem 1.1, the exponential base for counting trees is $2+\eta$ for any fixed $\eta>0$, at the price of a polynomial factor in $n$ whose degree grows like $\eta^{-1}\log(2/\eta)$; the same estimator extends to all patterns of bounded treewidth.
--
--   **Formalization Note** The algorithm is the paper's own §3.8 algorithm, written out as the charged program `countEmb η` (directed input) and `countEmbU η` (undirected input) in the cost monad `CapacitatedAssort.General.Work`; the probability is the fraction of the $2^L$ tapes of its bit budget $L$ on which the output is within relative error $\varepsilon$, and the operation count is bounded on every tape. Without the program, "there is an algorithm using … operations" would be trivially true.
--
--   Differences from the source:
--   - reading: "there is a randomized algorithm … using … arithmetic operations" → the paper's §3.8 algorithm as the program countEmb/countEmbU in the cost monad Work, every arithmetic operation, comparison, loop step and sampling attempt charged, linear-time median, parameters computed by charged loops; reason: without the program the existence claim is trivial; this is the paper's accounting (§2.11, §3.7, §3.8)
--   - reading: "A width-t decomposition of H can be found in k^{O(t+1)} time [ACP87]" and "For forests, … the separator from Lemma 3.2" → an optimal elimination ordering computed by the exact subset dynamic program (2^k k^{O(1)} operations), its elimination-forest decomposition (width tw(H)), and Lemma 3.4 for every pattern; reason: the cited routine is not written in the paper; this one is within the (2+η)^k factor, gives width tw(H) ≤ t, and gives |S| ≤ 2c for forests, so the bounds are the same
--   - reading: "for every fixed 0 < η ≤ 1 … n^{O(η⁻¹ log(2/η))}", "bounded treewidth t … n^{O(η⁻¹ log(2/η)·(t+1))}" → a universal a quantified before η, then ∀ η ∃ C (forest clauses) and ∀ η ∀ t ∃ C (treewidth clause), with factors (n+1)^{a η⁻¹ log(2/η)} and (n+1)^{a η⁻¹ log(2/η)(t+1)}; reason: the meaning of O(·) for a fixed η and a fixed t; the exponent constant must not depend on η
--   - encoding: graphs on n vertices, embeddings, n, log, fair random bits → SimpleGraph on Fin k / Fin n, directed graphs as arc sets Finset (Fin n × Fin n), N as the number of injective maps (embCount, dembCount), the factor (n+1), natural log, a uniform tape Fin L → Bool with L = embBits n k ε δ; reason: same instances; (n+1) only differs at n = 0, where the printed bound is 0
--   - generalization: a tree; a directed host graph → every acyclic SimpleGraph (forests, including the empty pattern k = 0, which the program answers exactly); directed hosts may contain self-loops; reason: trees are acyclic, so the tree clause is a special case; a loop is never used by an injective map of a loopless pattern, so on loop-free hosts the statement is the source's
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Theorem 1.2, p.2 (PDF p.3); proof §3, pp.18–27

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Algorithm
import Definitions.Def_PathCount2k_Supplement_Embedding
import Definitions.Def_PathCount2k_Supplement_TreeAlgorithm

open scoped Classical

namespace PathCount2k.Supplement

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026),
**Theorem 1.2** (Counting trees and beyond), p.2: "For every fixed `0 < η ≤ 1`, there is a
randomized algorithm with the following guarantee. Given a tree `H` on `k` vertices, an undirected
graph `G` on `n` vertices, and `0 < ε, δ < 1`, the algorithm returns an estimate `N̂` of the number
`N` of embeddings of `H` into `G` satisfying `Pr[|N̂ − N| ≤ εN] ≥ 1 − δ`, using
`(2 + η)^k n^{O(η⁻¹ log(2/η))} ε⁻² log(2/δ)` arithmetic operations. The same guarantee holds for
forests, as well as for arbitrary orientations of trees and forests in directed host graphs.
Furthermore, the same guarantee holds for pattern graphs `H` of bounded treewidth `t`, with an
extra multiplicative factor of `n^{O(η⁻¹ log(2/η)·(t+1))}` for the number of arithmetic
operations." Proof: §3, pp.18–27.

The algorithm is the paper's §3.8 algorithm, the charged program `countEmb η` (directed input) and
`countEmbU η` (undirected input), run on a tape of `embBits n k ε δ` fair bits (`16 T_samp` when
`2 ≤ k ≤ n`, Observation 3.3). There is a universal constant `a` such that for every `0 < η ≤ 1`:
1. there is `C` such that for every forest `H` (in particular every tree) and every undirected
   `G`, and for every orientation `PA` of a forest and every directed host `GA`, and all
   `0 < ε, δ < 1`: the fraction of tapes on which `|N̂ − N| ≤ εN` is at least `1 − δ`, and on every
   tape the number of charged operations is at most
   `C (2 + η)^k (n + 1)^{a η⁻¹ log(2/η)} ε⁻² log(2/δ)`;
2. for every `t` there is `C` such that the same holds for every undirected `H` of treewidth at
   most `t` (Definition 3.2) and every undirected `G`, with the operation bound multiplied by
   `(n + 1)^{a η⁻¹ log(2/η) (t + 1)}`.

**Formalization Note.** "There is a randomized algorithm … using … arithmetic operations" is read
as a statement about the paper's own algorithm, written out as a program in the cost monad
`CapacitatedAssort.General.Work`; without the program the claim would be trivial. The constant in
the exponent `O(η⁻¹ log(2/η))` is universal (quantified before `η`); only the leading constant may
depend on the fixed `η` (and on the fixed `t`). `n + 1` reads `n`; `log` is natural. The input is
the pattern itself: the program computes its decomposition. -/
theorem theorem_1_2 :
    ∃ a : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      (∃ C : ℝ,
        (∀ (k : ℕ) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj], H.IsAcyclic →
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ε δ : ℝ),
            0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (((Finset.univ.filter fun b : Fin (embBits n k ε δ) → Bool =>
                |((countEmbU η H G ε δ b).run 0).1 - (embCount H G : ℝ)| ≤
                  ε * (embCount H G : ℝ)).card : ℝ) / 2 ^ embBits n k ε δ ≥ 1 - δ) ∧
            ∀ b : Fin (embBits n k ε δ) → Bool,
              ((((countEmbU η H G ε δ b).run 0).2 : ℕ) : ℝ) ≤
                C * (2 + η) ^ k * ((n : ℝ) + 1) ^ (a * η⁻¹ * Real.log (2 / η)) *
                  ε ^ (-2 : ℤ) * Real.log (2 / δ)) ∧
        (∀ (k : ℕ) (PA : Finset (Fin k × Fin k)), IsForestOrientation PA →
          ∀ (n : ℕ) (GA : Finset (Fin n × Fin n)) (ε δ : ℝ),
            0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (((Finset.univ.filter fun b : Fin (embBits n k ε δ) → Bool =>
                |((countEmb η k PA n GA ε δ b).run 0).1 - (dembCount PA GA : ℝ)| ≤
                  ε * (dembCount PA GA : ℝ)).card : ℝ) / 2 ^ embBits n k ε δ ≥ 1 - δ) ∧
            ∀ b : Fin (embBits n k ε δ) → Bool,
              ((((countEmb η k PA n GA ε δ b).run 0).2 : ℕ) : ℝ) ≤
                C * (2 + η) ^ k * ((n : ℝ) + 1) ^ (a * η⁻¹ * Real.log (2 / η)) *
                  ε ^ (-2 : ℤ) * Real.log (2 / δ))) ∧
      ∀ t : ℕ, ∃ C : ℝ,
        ∀ (k : ℕ) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj], TwLe H t →
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ε δ : ℝ),
            0 < ε → ε < 1 → 0 < δ → δ < 1 →
            (((Finset.univ.filter fun b : Fin (embBits n k ε δ) → Bool =>
                |((countEmbU η H G ε δ b).run 0).1 - (embCount H G : ℝ)| ≤
                  ε * (embCount H G : ℝ)).card : ℝ) / 2 ^ embBits n k ε δ ≥ 1 - δ) ∧
            ∀ b : Fin (embBits n k ε δ) → Bool,
              ((((countEmbU η H G ε δ b).run 0).2 : ℕ) : ℝ) ≤
                C * (2 + η) ^ k * ((n : ℝ) + 1) ^ (a * η⁻¹ * Real.log (2 / η)) *
                  ((n : ℝ) + 1) ^ (a * η⁻¹ * Real.log (2 / η) * ((t : ℝ) + 1)) *
                  ε ^ (-2 : ℤ) * Real.log (2 / δ) := by sorry

end PathCount2k.Supplement
