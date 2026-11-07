-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_9
-- name    : PathCount2k.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:42.088193+00:00
-- url     : https://prove2.me/theorems/b640c68f-c2b4-454b-8463-4bd709bbee10
-- title:
--   Lemma 2.9 — conditional fourth moment $\mathbb E_M[Z^4\mid g]\le3(1+2/D)^{k-1}(\sum_P\Delta_P^2)^2$
-- statement:
--   Fix the vertex vectors $g$ and an integer $D\ge1$, and let the auxiliary matrices have independent $N(0,1/D)$ entries. Then
--   $$
--   \mathbb E_M\big[Z^4\mid g\big]\le3\Big(1+\frac2D\Big)^{k-1}\Big(\sum_{P\in\mathcal P_k}\Delta_P^2\Big)^2.
--   $$
--
--   Averaging over the matrices costs at most a factor $3\alpha_D^{k-1}$, which is $O(1)$ for $D=k$.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
--   - encoding: g_v ∼ N(0, I_k) independent; entries of M_{i,v} standard Gaussian divided by √D, independent → vecLaw = Measure.pi of gaussianReal 0 1; matLaw = Measure.pi of gaussianReal 0 (1/D); jointLaw their product; reason: the law of X/√D for X ∼ N(0,1) is N(0, 1/D); same distributions
--   - encoding: E_M[Z⁴ | g] for every fixed g → the integral of Z(g, ·)⁴ against matLaw n k D, for every g; reason: the matrices are independent of g; this is how the paper uses the conditional expectation
--   - encoding: the expectation E_M[Z⁴ | g] → Integrable … ∧ the Bochner integral bound; reason: Lean's integral is 0 on a non-integrable function; the paper's expectation exists, so stating integrability excludes only the junk case
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.9, p.10

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.9** (Conditional fourth-moment bound), p.10: "For every fixed choice
of vertex vectors `g` and every integer `D ≥ 1`, `E_M[Z⁴ | g] ≤ 3(1 + 2/D)^{k−1} (∑_{P∈P_k} Δ_P²)²`."

**Formalization Note.** `E_M[· | g]` is the integral over the matrices only, against
`matLaw n k D`, with `g` fixed; the integrability of `Z⁴` in the matrices is stated too. Stated
for every `k ≥ 1` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_9 (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D)
    (g : VecSample n k) :
    Integrable (fun M => Z n E k D (g, M) ^ 4) (matLaw n k D) ∧
      ∫ M, Z n E k D (g, M) ^ 4 ∂(matLaw n k D) ≤
        3 * (1 + 2 / (D : ℝ)) ^ (k - 1) * (∑ P ∈ paths n E k, Delta g P ^ 2) ^ 2 := by sorry

end PathCount2k
