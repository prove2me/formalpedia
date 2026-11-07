-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_2
-- name    : PathCount2k.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:20.270907+00:00
-- url     : https://prove2.me/theorems/8f706f24-75c8-4d40-9fee-f63dfb423cad
-- title:
--   Lemma 2.2 — $\mathbb E_g[\Delta_P^2]=k!$
-- statement:
--   Let the vertex vectors $g_v\in\mathbb R^k$ be independent standard Gaussian vectors. For every directed $k$-vertex path $P\in\mathcal P_k$,
--   $$
--   \mathbb E_g\big[\Delta_P^2\big]=k!.
--   $$
--
--   Every path determinant has the same second moment, whatever the overlaps between paths; this gives unbiasedness of the estimator.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n → every k; reason: true for every k; specializes
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.2, p.5

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.2**, p.5: "For every `P ∈ P_k`, `E_g[Δ_P²] = k!`", where the vertex
vectors are independent standard Gaussian vectors `g_v ∼ N(0, I_k)` (§2.3, p.5).

**Formalization Note.** `E_g` is the integral against `vecLaw n k`. Stated for every `k`
(the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_2 (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ) (P : Fin k → Fin n)
    (hP : P ∈ paths n E k) :
    ∫ g, Delta g P ^ 2 ∂(vecLaw n k) = (Nat.factorial k : ℝ) := by sorry

end PathCount2k
