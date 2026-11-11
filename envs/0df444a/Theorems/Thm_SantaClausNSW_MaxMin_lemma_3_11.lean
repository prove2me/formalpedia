-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_11
-- name    : SantaClausNSW.MaxMin.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:35:17.120087+00:00
-- url     : https://prove2.me/theorems/01130699-0fe6-4670-8c67-99e93a9a82b4
-- title:
--   Lemma 3.11 — repeated guiding-tree rounding with a random coloring: Pr[v_i(Ḡ_i) < V/(8h)] ≤ e^{−h r_i/16}
-- statement:
--   Let $V>0$ and an integer $h\ge1$, and consider a feasible configuration solution for normalized monotone subadditive valuations; $r_i$ is the total mass of agent $i$'s nonempty configurations. Suppose every nonempty configuration $S$ of agent $i$ satisfies $v_i(S)\ge V$ and $v_i(\{j\})\le V/(16h)$ for every $j\in S$. Then there is a randomized procedure returning a feasible allocation $\bar G$ such that for every agent $i$
--   $$\Pr\Big[v_i(\bar G_i)<\frac{V}{8h}\Big]\le e^{-hr_i/16}.$$
--   Theorem 3.12 uses it for the agents that do not receive a core configuration.
--
--   Differences from the source:
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - reading: 'there is a randomized procedure that returns a feasible allocation' → there is a law on feasible allocations satisfying the bound for every agent; reason: the lemma claims no running time; its content is the existence of the outcome law
--   - encoding: each nonempty configuration S of agent i → each nonempty S with y_{i,S} > 0; reason: configurations are those of positive mass (p. 11)
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), pp. 27–28, Lemma 3.11

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Machine
import Definitions.Def_SantaClausNSW_MaxMin_Valuations

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.11** (p. 27). Let `V > 0` and an integer `h ≥ 1`, and let `y` be a feasible
configuration solution for normalized monotone subadditive valuations; `r_i` is the total mass of
agent `i`'s nonempty configurations. If every nonempty configuration `S` of agent `i` (of positive
mass) has `v_i(S) ≥ V` and `v_i({j}) ≤ V/(16h)` for every `j ∈ S`, then there is a randomized
procedure — a law of feasible allocations `Ḡ` — with `Pr[v_i(Ḡ_i) < V/(8h)] ≤ e^{−h r_i/16}` for
every agent `i`. -/
theorem lemma_3_11 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsValuation (v i) ∧ IsSubadditive (v i))
    (y : Fin n → Finset (Fin m) → ℝ) (hy : IsConfigSolution y) (V : ℝ) (hV : 0 < V)
    (h : ℕ) (hh : 1 ≤ h)
    (hcfg : ∀ i S, S ≠ ∅ → 0 < y i S → V ≤ v i S ∧ ∀ j ∈ S, v i {j} ≤ V / (16 * h)) :
    ∃ μ : PMF (Fin n → Finset (Fin m)), (∀ G ∈ μ.support, IsAllocation G) ∧
      ∀ i : Fin n, probOf μ (fun G => v i (G i) < V / (8 * h)) ≤
        Real.exp (-((h : ℝ) * (∑ S ∈ (Finset.univ.filter fun S : Finset (Fin m) => S ≠ ∅),
          y i S)) / 16) := by sorry

end SantaClausNSW.MaxMin
