-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_12
-- name    : PathCount2k.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:53.651418+00:00
-- url     : https://prove2.me/theorems/407f108f-694f-4177-92e9-a456e55317bb
-- title:
--   Lemma 2.12 — $\mathbb E_g[(\sum_P\Delta_P^2)^2]\le K_k(k!)^2N^2$
-- statement:
--   Let the vertex vectors be independent standard Gaussian vectors. Then
--   $$
--   \mathbb E_g\Big[\Big(\sum_{P\in\mathcal P_k}\Delta_P^2\Big)^2\Big]\le K_k\,(k!)^2N^2.
--   $$
--
--   Overlapping paths share vectors; the bound holds without any independence between their determinants.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n → every k; reason: true for every k; specializes
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - encoding: the expectation E_g[(Σ_P Δ_P²)²] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.12, p.12

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.12** (Sum of squared determinants), p.12: "We have
`E_g[(∑_{P∈P_k} Δ_P²)²] ≤ K_k(k!)²N²`."

**Formalization Note.** `E_g` is the integral against `vecLaw n k`; the integrability of the
left side is stated too. Stated for every `k` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_12 (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ) :
    Integrable (fun g => (∑ P ∈ paths n E k, Delta g P ^ 2) ^ 2) (vecLaw n k) ∧
      ∫ g, (∑ P ∈ paths n E k, Delta g P ^ 2) ^ 2 ∂(vecLaw n k) ≤
        Kk k * (Nat.factorial k : ℝ) ^ 2 * (N n E k : ℝ) ^ 2 := by sorry

end PathCount2k
