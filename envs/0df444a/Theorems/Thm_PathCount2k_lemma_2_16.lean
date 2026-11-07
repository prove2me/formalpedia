-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_16
-- name    : PathCount2k.lemma_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:49.545553+00:00
-- url     : https://prove2.me/theorems/2eb02aa5-2ca5-4018-96cc-124bcc4db3c7
-- title:
--   Lemma 2.16 — correctness of the dynamic program
-- statement:
--   Fix integer samples $g_v\in\mathbb Z^k$ and $H_{i,v}\in\mathbb Z^{D\times D}$, $D\ge1$. The tables computed by the dynamic program of §2.10 satisfy equation (1): for every layer $1\le p\le k$, vertex $v$ and $S\subseteq[k]$ with $|S|=p$,
--   $$
--   X_{p,v}[S]=\sum_{W\in W_p(v)}c_W[S]\,\rho_W\in\mathbb Z^{1\times D}.
--   $$
--   Moreover $zb_0=Z_0$, so the output $(zb_0)^2/(k!D^{k-1})$ is exactly the finite estimator $Y_0$.
--
--   The dynamic program evaluates the sum over all paths without enumerating them.
--
--   Differences from the source:
--
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1 and every n; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - encoding: the tables X_{p,v}[S] and z b₀ computed by the program of §2.10 → the values of the charged programs layer, dp and dpOutput (the step-3 output (z b₀)²/(k! D^{k−1}) as an exact rational); subsets as bit masks maskOf S; the graph as an arc list A without repetitions, E = A.toFinset; Y₀ evaluated at the samples cast to ℝ; reason: the program performs exactly steps 1–3; same instances
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.16, p.15 (equation (1), Definition 2.18, p.14)

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_Finite
import Definitions.Def_PathCount2k_DP

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.16** (Correctness of the dynamic program), p.15: "For every fixed choice
of the sampled vectors and matrices, the computed tables satisfy (1). Moreover, `z b₀ = Z₀`, so the
output is exactly the finite estimator `Y₀`."

Equation (1) (Definition 2.18, p.14) is `X_{p,v}[S] = ∑_{W∈W_p(v)} c_W[S] ρ_W ∈ ℤ^{1×D}` for
`p ∈ [k]`, `v ∈ V` and `|S| = p`, with `c_W[S]` the exterior coordinates of `Φ(W)` and `ρ_W` the
auxiliary row of the walk `W` (Definition 2.17).

**Formalization Note.** The tables are the values of the charged program `layer` (the subset `S`
is its mask `maskOf S`), `z b₀` is the value of `dp`, and the input graph is the arc list `A`
without repetitions, `E = A.toFinset`. The output `(z b₀)²/(k! D^{k−1})` of step 3 is the value of
`dpOutput` (an exact rational), compared with `Y₀` at the samples cast to `ℝ`. Stated for every `k ≥ 1` and every `D ≥ 1` (the paper's §2.10
uses `2 ≤ k ≤ n`). -/
theorem lemma_2_16 (n : ℕ) (A : List (Fin n × Fin n)) (hA : A.Nodup) (k D : ℕ) (hk : 1 ≤ k)
    (hD : 1 ≤ D) (g : Fin n → Fin k → ℤ) (H : Fin k → Fin n → Fin D → Fin D → ℤ) :
    (∀ (p : ℕ) (hp : 1 ≤ p) (hpk : p ≤ k) (v : Fin n) (S : Finset (Fin k)), S.card = p →
      ((layer n k D A g H p).run 0).1 v (maskOf S) =
        fun b => ∑ W ∈ walksTo n A.toFinset p v, Phi g W S * walkRow H hpk W b) ∧
      ((dp n k D A g H).run 0).1 = Z0 n A.toFinset k D g H ∧
      ((((dpOutput n k D A g H).run 0).1 : ℚ) : ℝ) =
        Y0 n A.toFinset k D (fun v j => (g v j : ℝ), fun i v a b => (H i v a b : ℝ)) := by sorry

end PathCount2k
