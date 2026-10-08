-- Prove2me | Theorems.Thm_SingleMachinePrec_Biclique_value_identity
-- name    : SingleMachinePrec.Biclique.value_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:22:55.447011+00:00
-- url     : https://prove2.me/theorems/ae90fbac-d166-4ee7-ba98-a92b650a569f
-- title:
--   §9, p. 666 — val(σ) = Σᵢ (σ(i+1) − σ(i))·i = n² − Σᵢ σ(i)
-- statement:
--   Let $G=(U,V,E)$ be an $n$-by-$n$ bipartite graph and $\sigma$ any schedule (any ordering) of all the jobs $U\cup V$ of $S_G$. For $i\ge1$ let $\sigma(i)$ be the number of jobs of $V$ scheduled before $i$ jobs of $U$ have been scheduled. Then $\sigma(n+1)=n$, and
--
--   $$\mathrm{val}(\sigma)=\sum_{i=1}^{n}\bigl(\sigma(i+1)-\sigma(i)\bigr)\,i=n^2-\sum_{i=1}^{n}\sigma(i).$$
--
--   The identity expresses the objective of $S_G$ through the profile $\sigma(1)\le\dots\le\sigma(n)$ of the schedule's "work line" in the two-dimensional Gantt chart; it turns the lower bound of Lemma 9.1 into an upper bound on $\sum_i\sigma(i)$.
--
--   **Formalization Note** The paper states this for an optimal schedule $\sigma^*$ and sets $\sigma^*(n+1)=n$ by convention; here it is stated for every ordering of the jobs (feasibility is not needed), and $\sigma(n+1)=n$ is a consequence of the definition of $\sigma(i)$, stated as the first conclusion.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 666, §9, proof of Lemma 9.1 (displayed identity)

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- §9, p. 666 (proof of Lemma 9.1, value identity). Let `G = (U, V, E)` be an `n`-by-`n`
bipartite graph and `l` any sequence of all the jobs `U ∪ V` of `S_G`. With `σ(i)` the number of
jobs of `V` scheduled before `i` jobs of `U` have been scheduled (`vBefore l i`), one has
`σ(n + 1) = n`, and the value of `l` is
`Σ_{i=1}^{n} (σ(i + 1) − σ(i)) · i = n² − Σ_{i=1}^{n} σ(i)`. -/
theorem value_identity {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (n : ℕ) (hU : Fintype.card U = n) (hV : Fintype.card V = n) (l : List (U ⊕ V))
    (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l) :
    vBefore l (n + 1) = n ∧
      valSG l = ∑ i ∈ Finset.Icc 1 n, ((vBefore l (i + 1) : ℝ) - (vBefore l i : ℝ)) * (i : ℝ) ∧
      valSG l = (n : ℝ) ^ 2 - ∑ i ∈ Finset.Icc 1 n, (vBefore l i : ℝ) := by sorry

end SingleMachinePrec.Biclique
