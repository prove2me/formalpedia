-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_demand_routing
-- name    : PersistClust.Count.theorem_4_5_demand_routing
-- status  : Open
-- author  : @fabianroll
-- created : 2026-10-12T05:57:45.817502+00:00
-- url     : https://prove2.me/theorems/0326b504-cda7-4dcd-8630-c2948cd5b922
-- title:
--   Theorem 4.5, demand routing: prominent and high far south-east copies route injectively under the interleaving
-- statement:
--   This is the demand-routing step in the proof of Theorem 4.5 of RR-6968: under a strong $\varepsilon$-interleaving above $\alpha$ between two tame $0$-dimensional persistence modules, the off-diagonal copies of the $X$-diagram that cannot be absorbed by the diagonal — prominent copies (points of $Q^{NE}_\alpha$ admitting no diagonal point $\varepsilon$-close in both coordinates) and high far south-east copies (birth above $\alpha + \varepsilon$, more than $2\varepsilon$ above the death) — can be routed injectively into the copies of the $Y$-diagram, with prominent copies landing $\varepsilon$-close in both coordinates and high far south-east copies landing $\varepsilon$-close in the birth coordinate on points that again lie in $Q^{SE}_\alpha$.
--
--   Formally: for two finite-type modules $X, Y$ strongly $\varepsilon$-interleaved above $\alpha$, there is an injection $F$ from the demanding copies of $D_X = \operatorname{mult}(r_X)$ to the copies of $D_Y$ such that $F$ maps prominent copies to $\varepsilon$-close copies (both coordinates) and high far south-east copies to south-east copies $\varepsilon$-close in the birth coordinate.
--
--   Together with the assembly child `theorem_4_5_matching_assembly` — which turns two such routings (one per direction) into the multi-bijection with guarantees (i)–(iv) via a Schröder–Bernstein argument — this yields the gate `theorem_4_5_gate_matching`. The routing is where the interleaving does its work: prominent $X$-bars must have $Y$-partners born and dying within $\varepsilon$ (window inequalities, census counting, image-birth transport), and high far south-east bars must have birth-close south-east partners.
--
--   **Formalization Note** The demand predicates are those of `PersistClust_Count_MatchingGate`; the modules enter through `FiltrationLaw`, `IsTameModule`, and `StrongInterleavingAbove` as defined in `PersistClust_Count_MatchingCensus`.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 18–21, the partner-routing construction in the proof of Theorem 4.5; stated with the demand predicates of the assembly step

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

namespace PersistClust.Count

theorem theorem_4_5_demand_routing
    {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (hIL : StrongInterleavingAbove stageX JX stageY JY hLawX hLawY α ε hε) :
    ∃ F : {a : offD (mult (rankFn stageX JX)) // DemandsOff α ε a}
           → offD (mult (rankFn stageY JY)),
      Function.Injective F ∧
      (∀ a, PromQNE α ε a.1 → CloseCopy2 ε a.1 (F a)) ∧
      (∀ a, offPt a.1 ∈ QSE α → CloseCopy1 ε a.1 (F a) ∧ offPt (F a) ∈ QSE α) := by sorry

end PersistClust.Count
