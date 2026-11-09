-- Prove2me | Theorems.Thm_WeldedPath_theorem_4_1
-- name    : WeldedPath.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:25:26.713675+00:00
-- url     : https://prove2.me/theorems/d48be8d6-953d-4f57-a331-af86240bf352
-- title:
--   Theorem 4.1 — pathfinding in welded trees needs $\Omega((N/(n+1))^{1/3})$ queries
-- statement:
--   Let $n\ge 16$ be even, $l\in[2,n-4]$, $N=2^n$, $N_l=2^{n-l}$ and $\epsilon_l=2^{-l}$. Any quantum algorithm $A$ making $q\ge 1$ queries to the welded trees oracle $O^{(wt)}_\sigma$ with $\sigma\sim D_{\mathrm{sing}}$ satisfies
--   $$
--   \Pr[A\text{ outputs a path from entrance to exit}]\ =\ O\!\left(\frac{q}{N_l}+q^2\epsilon_l+\frac{n\,q^3}{N}\right),
--   $$
--   where the probability is over $\sigma$ and the measurement outcomes of $A$. Precisely:
--
--   1. there is an absolute constant $C>0$ such that for all such $n$, $l$, every valid instance, every finite workspace, every $q\ge1$, every algorithm and every output map, the success probability is at most $C\,(q/2^{n-l}+q^2/2^l+n\,q^3/2^n)$;
--   2. there is a choice $l=L(n)\in[2,n-4]$ such that for every constant $p\in(0,1]$ there is $c>0$ with: whenever the success probability is at least $p$,
--   $$
--   q\ \ge\ c\left(\frac{N}{n+1}\right)^{1/3}.
--   $$
--
--   A quantum walk reaches the exit in polynomially many queries, but no quantum algorithm can output a path to it with fewer than about $(2^n/n)^{1/3}$ queries.
--
--   Differences from the source:
--   - generalization: a path (z_0 = 0, α_1, z_1, …, α_m, z_m) with pairwise distinct labels and m ≥ n → any nonempty colored walk from label 0 to the exit label along oracle edges, each step changing the label; reason: every such path is a walk, so a bound on walks bounds paths; loops can be erased without queries (p.22)
--   - generalization: one fixed instance G_n with one fixed coloring (pp.14–15) → every valid weld (one bipartite cycle on the leaves) and every proper 3-coloring, with C independent of them; reason: the fixed instance is one of them
--   - reading: O(q/N_l + q²·ϵ_l + n·q³/N) → one absolute constant C > 0 for all even n ≥ 16, l ∈ [2, n − 4], instances, workspaces, q ≥ 1, algorithms and output maps; reason: the bound is uniform in all parameters
--   - reading: for a suitable choice of l, constant success probability requires Ω((N/(n + 1))^{1/3}) queries → ∃ L(n) ∈ [2, n − 4] such that ∀ p ∈ (0, 1] ∃ c > 0 ∀ even n ≥ 16: success ≥ p ⇒ q ≥ c(2^n/(n + 1))^{1/3}; reason: the stronger reading: l is chosen before the success probability (the proof takes l = ⌊2n/3⌋)
--   - encoding: algorithm A_q O ⋯ A_1 O A_0|0⟩ and its output → QAlgorithms.QueryAlg with any unit start state and finite workspace; the output list is a function of the computational-basis outcome; reason: a unit start state is |0⟩ followed by A_0; measuring the whole register is the general output
--   - encoding: labels in (2n+1)-bit registers, colors C, σ_edge ∈ ∏_b Sym(E_b), D_sing = D_prod | S → binary value (most significant bit first), Fin 3, one permutation of E_n preserving every E_b and fixing other edges, uniform average over the finite support; reason: bijective encodings of the same objects and distributions
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Theorem 4.1, p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_successProb

namespace WeldedPath

open QAlgorithms

/-- **Theorem 4.1** (Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic
Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…),
Theorem 4.1, p.26). Assume that `n ≥ 16` is even and `l ∈ [2, n − 4]`. Any quantum algorithm `A`
making `q` queries to the welded trees oracle `O^{(wt)}_σ` with `σ ∼ D_sing` satisfies
`Pr[A outputs a path from entrance to exit] = O(q/N_l + q²·ϵ_l + n·q³/N)` (48), with
`N = 2^n`, `N_l = 2^{n−l}`, `ϵ_l = 2^{−l}`. For a suitable choice of `l`, constant success
probability requires `Ω((N/(n + 1))^{1/3})` queries.

**Formalization Note.**
1. `O(·)` is one absolute constant `C`, chosen before `n`, `l`, the instance, the workspace, `q`,
   the algorithm and its output map.
2. "A suitable choice of `l`" is one choice `L n ∈ [2, n − 4]` for each `n`, fixed before the
   success probability `p`; then `c > 0` depends on `p` only.
3. The algorithm is the published `QAlgorithms.QueryAlg` with query register
   `(2n+1)`-bit label × color and `(2n+1)`-bit answer register, any finite workspace `W`, and
   `q ≥ 1` queries ("every algorithm makes at least 1 query", p.9). Its output is read off the
   final computational-basis measurement by `out`, as the list of steps `(α_i, z_i)`.
4. Success is an entrance–exit walk (`IsEntranceExitWalk`), which includes every path.
5. The bound holds for every valid weld and proper coloring (`WeldedInstance.IsValid`). -/
theorem theorem_4_1 :
    (∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      G.successProb l A out ≤
        C * ((q : ℝ) / 2 ^ (n - l) + (q : ℝ) ^ 2 / 2 ^ l + (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n)) ∧
    (∃ L : ℕ → ℕ, (∀ n : ℕ, Even n → 16 ≤ n → 2 ≤ L n ∧ L n ≤ n - 4) ∧
      ∀ p : ℝ, 0 < p → p ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, Even n → 16 ≤ n →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      p ≤ G.successProb (L n) A out →
        c * ((2 : ℝ) ^ n / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 3) ≤ (q : ℝ)) := by sorry

end WeldedPath
