-- Prove2me | Theorems.Thm_SingleMachinePrec_Biclique_upper_bound_schedule
-- name    : SingleMachinePrec.Biclique.upper_bound_schedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:22:26.888984+00:00
-- url     : https://prove2.me/theorems/e208faf5-7971-4619-a0b4-55eb47936c0c
-- title:
--   §9, p. 666 — the schedule U∖A → B → A → V∖B is feasible and has value n² − |A|·|B|
-- statement:
--   Let $G=(U,V,E)$ be an $n$-by-$n$ bipartite graph ($|U|=|V|=n$), $S_G$ its bipartite scheduling instance, and $(A,B)$ an edge biclique of $G$ ($A\subseteq U$, $B\subseteq V$, $A\times B\subseteq E$). Then a schedule of all jobs of $S_G$ in the block order
--   $$U\setminus A\;\to\;B\;\to\;A\;\to\;V\setminus B$$
--   exists, and every such schedule $\sigma$ is feasible for $S_G$ and has value
--   $$\mathrm{val}(\sigma)=(n-|A|)\,|B|+n\,(n-|B|)=n^2-|A|\cdot|B| .$$
--
--   This is the upper half of Lemma 9.1: applied to a maximum edge biclique it gives $\mathrm{val}(\sigma^*)\le n^2-\mathrm{MEB}(G)$.
--
--   **Formalization Note** The paper writes $\mathrm{val}(\sigma)\le\dots=n^2-|A|\cdot|B|$; the value is in fact equal to $n^2-|A|\cdot|B|$, which is what is stated. Feasibility, which the paper argues from the absence of precedence constraints from $A$ to $B$, is part of the conclusion.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 666, §9, proof of Lemma 9.1 (upper bound)

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- §9, p. 666 (proof of Lemma 9.1, upper bound). Let `G = (U, V, E)` be an `n`-by-`n` bipartite
graph and `(A, B)` an edge biclique of `G`. A sequence of all the jobs of `S_G` in the order
`U \ A → B → A → V \ B` exists; every such sequence observes the precedence constraints
`P = (U × V) \ E` of `S_G`, and its value is `n² − |A| · |B|`. -/
theorem upper_bound_schedule {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    [DecidableEq V] (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (A : Finset U) (B : Finset V) (hAB : IsEdgeBiclique E A B) :
    (∃ l : List (U ⊕ V), InBlockOrder A B l) ∧
      ∀ l : List (U ⊕ V), InBlockOrder A B l →
        LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l ∧
          valSG l = (n : ℝ) ^ 2 - (A.card : ℝ) * (B.card : ℝ) := by sorry

end SingleMachinePrec.Biclique
