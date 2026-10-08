-- Prove2me | Theorems.Thm_SingleMachinePrec_Biclique_prefix_biclique_bound
-- name    : SingleMachinePrec.Biclique.prefix_biclique_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:23:20.48296+00:00
-- url     : https://prove2.me/theorems/2c80c8d3-70ac-4998-ac6d-de6786347aed
-- title:
--   §9, p. 666 — σ(i)(n − i + 1) ≤ an² and σ(i) ≤ n for i = 1, …, n
-- statement:
--   Let $G=(U,V,E)$ be an $n$-by-$n$ bipartite graph whose maximum edge biclique has value $a n^2$, and let $\sigma$ be a feasible schedule of $S_G$. For $i\ge1$ let $\sigma(i)$ be the number of jobs of $V$ scheduled before $i$ jobs of $U$ have been scheduled. Then for every $i=1,\dots,n$,
--
--   $$\sigma(i)\,(n-i+1)\le a n^2\qquad\text{and}\qquad\sigma(i)\le n .$$
--
--   The first bound holds because the $n-i+1$ jobs of $U$ not yet scheduled and the $\sigma(i)$ jobs of $V$ already scheduled at that point form an edge biclique of $G$; combined with the value identity it yields the lower bound of Lemma 9.1.
--
--   **Formalization Note** The paper states this for an optimal schedule $\sigma^*$; it holds for every feasible schedule, which is what is stated. The number $a$ is any real with $\mathrm{MEB}(G)=a n^2$; no range for $a$ is needed here. The factor $n-i+1$ is computed in the reals.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 666, §9, proof of Lemma 9.1 (bounds on σ*(i))

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- §9, p. 666 (proof of Lemma 9.1, per-prefix bound). Let `G = (U, V, E)` be an `n`-by-`n`
bipartite graph whose maximum edge biclique has value `a n²`, and let `l` be a feasible schedule
of `S_G` (a sequence of all the jobs observing `P = (U × V) \ E`). With `σ(i)` the number of jobs
of `V` scheduled before `i` jobs of `U` have been scheduled, for every `i = 1, …, n`,
`σ(i) (n − i + 1) ≤ a n²` and `σ(i) ≤ n`. -/
theorem prefix_biclique_bound {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    [DecidableEq V] (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (a : ℝ) (hmax : (maxBicliqueValue E : ℝ) = a * (n : ℝ) ^ 2)
    (l : List (U ⊕ V)) (hl : LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (vBefore l i : ℝ) * ((n : ℝ) - (i : ℝ) + 1) ≤ a * (n : ℝ) ^ 2 ∧ vBefore l i ≤ n := by sorry

end SingleMachinePrec.Biclique
