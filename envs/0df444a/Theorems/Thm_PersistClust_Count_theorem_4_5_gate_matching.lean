-- Prove2me | Theorems.Thm_PersistClust_Count_theorem_4_5_gate_matching
-- name    : PersistClust.Count.theorem_4_5_gate_matching
-- status  : Open
-- author  : @fabianroll
-- created : 2026-10-12T05:57:48.17218+00:00
-- url     : https://prove2.me/theorems/ff828e65-33b6-4791-b71e-6ccb08c9be0e
-- title:
--   Theorem 4.5, algebraic gate: strong interleaving above $\alpha$ of tame modules yields the multi-bijection (i)–(iv)
-- statement:
--   This is the algebraic gate of the proof of Theorem 4.5 of RR-6968: a strong $\varepsilon$-interleaving above a level $\alpha$ between two tame $0$-dimensional persistence modules yields the multi-bijection between their $0$-th persistence diagrams with the matching guarantees (i)–(iv).
--
--   Let $X$ and $Y$ be two decreasing filtrations of stages over $\mathbb{R}$ with the same-stage component relations, each a finite-type module (pointwise finiteness of component classes, a finite critical set with rigid class structure on critical-free windows, and eventual emptiness). Write $r_X$ and $r_Y$ for their $0$-th rank functions and $D_X = \operatorname{mult}(r_X)$, $D_Y = \operatorname{mult}(r_Y)$ for the associated persistence diagrams. Suppose the two modules are strongly $\varepsilon$-interleaved above $\alpha$ for some $\varepsilon \ge 0$: there are component-class maps $\varphi_\beta : X^\beta \to Y^{\beta-\varepsilon}$ and $\psi_\beta : Y^\beta \to X^{\beta-\varepsilon}$ for $\beta \ge \alpha$ commuting with the coarsening maps (naturality) and composing to the two-step coarsening ($\varphi_{\beta-\varepsilon} \circ \psi_\beta$ and its mirror).
--
--   Then there is a bijection $\gamma$ between all copies of $D_X$ and all copies of $D_Y$ such that:
--
--   1. every copy of a point of $Q^{NE}_\alpha$ is mapped $\varepsilon$-closely in both coordinates, in both directions (assertions (i), (ii));
--   2. every copy of a point of $Q^{SE}_\alpha$ is mapped $\varepsilon$-closely in the birth coordinate, in both directions (assertions (iii), (iv)).
--
--   This is the module-level statement of the matching half of Theorem 4.5: the geometric half (the interleaving of the superlevel and Rips filtrations of the sampled data) is published separately as `theorem_4_5_interleaving_corrected`, and the final assembly from demand routings as `theorem_4_5_matching_assembly`. The present gate composes the routing of demanding copies (the demand-routing child) with that assembly.
--
--   **Formalization Note** The conclusion is stated on `Copies`, the copy type of a diagram (off-diagonal copies plus diagonal slots); `SatisfiesIIV` is the four-clause guarantee. All structure enters through `FiltrationLaw`, `IsTameModule`, and `StrongInterleavingAbove` as defined in `PersistClust_Count_MatchingCensus`.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968, 2009, pp. 18–21, the matching half of the proof of Theorem 4.5 (via Lemma 4.6's role); module-level statement with the demand-routing and assembly children

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

namespace PersistClust.Count

theorem theorem_4_5_gate_matching
    {ιX ιY : Type*} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    (hIL : StrongInterleavingAbove stageX JX stageY JY hLawX hLawY α ε hε) :
    ∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ α ε := by sorry

end PersistClust.Count
