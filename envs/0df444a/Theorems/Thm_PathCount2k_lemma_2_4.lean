-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_4
-- name    : PathCount2k.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:24.938213+00:00
-- url     : https://prove2.me/theorems/0d33c8ab-a183-4ac9-8b3a-17ca634c1d24
-- title:
--   Lemma 2.4 — unbiasedness: $\mathbb E[Z^2]=Nk!$ and $\mathbb E[Y]=N$
-- statement:
--   Let the vertex vectors be independent standard Gaussian vectors and the auxiliary matrices independent with $N(0,1/D)$ entries, $D\ge1$. For $Z=\sum_{P\in\mathcal P_k}\Delta_P\chi(P)$ and $Y=Z^2/k!$,
--   $$
--   \mathbb E[Z^2]=N\,k!,\qquad \mathbb E[Y]=N.
--   $$
--
--   One trial is an unbiased estimator of the number $N$ of directed $k$-vertex paths.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.4, p.7

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.4** (Unbiasedness), p.7: "For every `D ≥ 1`, `E[Z²] = N k!` and
`E[Y] = N`", for `Z = ∑_{P ∈ P_k} Δ_P χ(P)` and `Y = Z²/k!` (Definition 2.9) under independent
Gaussian vertex vectors and auxiliary matrices.

**Formalization Note.** `E` is the integral against `jointLaw n k D`. Stated for every `k ≥ 1`
(the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_4 (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) :
    ∫ ω, Z n E k D ω ^ 2 ∂(jointLaw n k D) = (N n E k : ℝ) * (Nat.factorial k : ℝ) ∧
      ∫ ω, Y n E k D ω ∂(jointLaw n k D) = (N n E k : ℝ) := by sorry

end PathCount2k
