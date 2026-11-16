-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_Supplement_theorem_1_3
-- name    : ShortestPlanarDisjoint.Main.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:35:33.174201+00:00
-- url     : https://prove2.me/theorems/6ed290a8-1be5-467d-bd4e-d7250d2d9a12
-- title:
--   Theorem 1.3 (companion theorem; not used in the proof of the goal) — Pairs on different assigned faces
-- statement:
--   Let $G$ be a finite simple undirected planar graph on $n$ vertices, with $2k$ distinct terminals grouped into $k$ prescribed pairs. Each terminal is assigned to a corner of an incident specified face of a supplied embedding. Let $f$ count precisely the faces receiving terminals. Suppose that the two endpoints of every prescribed pair have different assigned face labels. There is no restriction on $k$ beyond the distinctness of the $2k$ terminals. Edge costs $w(e)$ are nonnegative integers, including zero, with $w(e)\le W$ on every edge.
--
--   There exist one finite randomized program $P$ and natural constants $A>0,a,b,d$, independent of $n,k,f,W$, the graph, the embedding and the random tape, such that, with $N=\max(2,n)$, the program finds pairwise vertex-disjoint simple paths joining every prescribed pair and minimizing their total original cost, or correctly reports infeasibility, with success probability at least $2/3$, within
--
--   $$
--   T=A N^{af+b}(W+1)^d
--   $$
--
--   bit transitions on every random tape. All returned path lists validate as linkages; a failure may report infeasibility or return a nonoptimal linkage. For every $0<\delta<1/2$, there is a positive repetition count $r$, independent of the instance, satisfying
--
--   $$
--   r\le A\left(1+\left\lceil\frac{\log(1/\delta)}{\log 2}\right\rceil\right),
--   $$
--
--   such that the same program, supplied with $r$, succeeds with probability at least $1-\delta$ within $rT$ transitions. The envelope contains no factor depending on $k$. For each fixed polynomial weight exponent $C$, substituting $W\le n^C$ gives the stated $n^{O(f)}$ bound; arbitrary integer costs retain the polynomial factor in $W+1$.
--
--   This companion theorem gives polynomial-time optimization for a fixed number of used terminal faces, even when the number of pairs grows with the graph. It retains disconnected and infeasible inputs and the empty linkage. It is an additional result of the paper, rather than a step used to prove the published mission goal, Theorem 1.1.
--
--   **Formalization Note.** The different-face condition is $\mathrm{label}(\mathrm{mate}(i))\ne\mathrm{label}(i)$ for every terminal label $i$. The representation and operational semantics are imported unchanged from the published mission. No connectedness, cellularity, positive-cost, supplied-gap or allowed-pairing hypothesis is added.
--
--   Differences from the source:
--
--   - encoding: finite simple undirected graphs, distinct paired terminals, minimum total cost and supplied incident faces → Fin-indexed RoutingInput, Linkage and FaceInput with explicit terminal corners and involutive mate pairing; reason: finite relabelling and one fixed orientation per unordered pair change no source instance, feasible linkage or objective
--   - encoding: a randomized search algorithm with the Section 1.1 time, success and amplification conventions → one finite multitape BitProgram with charged transitions, all-tape halting and legal decoded path outputs, success at least 2/3 and at least 1-delta after repetitions; reason: actual finite executions establish running time and return an original-cost optimum or correct infeasibility; there is no supplied correct oracle or assigned free runtime
--   - encoding: n^{O(f)} with the general-cost poly(W) factor and O(log(1/delta)) amplification → uniform natural witnesses A,a,b,d with N=max(2,n), time A N^{a f+b}(W+1)^d and positive repetitions at most A(1+ceil(log(1/delta)/log 2)); reason: witnesses precede all instance data; natural exponents and the small-input envelope cover each fixed source exponent, including every fixed polynomial weight exponent C
--   - generalization: used faces of a supplied planar embedding → componentwise planar rotations with used face labels consistent within components, allowing arbitrary groupings across components; reason: every source embedding induces these data; processing components separately uses at most f labels per component and preserves the different-face condition for every pair contained in a component, while split pairs are rejected
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Theorem 1.3 and Section 1.1 conventions, p. 2 (PDF p. 4); proof overview pp. 11–12 (PDF pp. 13–14), Corollary 5.11, p. 29 (PDF p. 31)

import Definitions.Def_ShortestPlanarDisjoint_Main_Embedding
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main.Supplement

/-- The different-assigned-face companion theorem. One finite program works
uniformly for every face count and number of pairs, including disconnected and
empty instances. The time envelope has no dependence on the pair count. -/
theorem theorem_1_3 :
    ∃ (P : BitProgram) (A a b d : ℕ), 0 < A ∧
      (∀ (n k f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
        E.embedding.IsPlanar →
        (∀ i : Fin (2 * k), E.label (I.pairing.mate i) ≠ E.label i) →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
        ExecutesSearch P I (numberBits 1 ++ E.bits)
          (A * (max 2 n) ^ (a * f + b) * (W + 1) ^ d) (2 / 3)) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ repetitions : ℕ, 0 < repetitions ∧
          repetitions ≤ A * (1 + ⌈Real.log (1 / δ) / Real.log 2⌉₊) ∧
          ∀ (n k f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
            E.embedding.IsPlanar →
            (∀ i : Fin (2 * k), E.label (I.pairing.mate i) ≠ E.label i) →
            (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
            ExecutesSearch P I (numberBits repetitions ++ E.bits)
              (repetitions * A * (max 2 n) ^ (a * f + b) * (W + 1) ^ d)
              (1 - δ)) := by sorry

end ShortestPlanarDisjoint.Main.Supplement
