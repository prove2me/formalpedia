-- Prove2me | Theorems.Thm_RunIntersect_Tight_theorem_1
-- name    : RunIntersect.Tight.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:06.59617+00:00
-- url     : https://prove2.me/theorems/e64438e0-cde6-4707-af9c-955e11756a37
-- title:
--   Theorem 1, p. 1022 — if V(G_α) ∩ V(G_ω) is a node or an edge and G_α is two-laminar β-acyclic, S_G decomposes into S_{G_α} and S_{G_ω}
-- statement:
--   Let $G=(V,E)$ be a hypergraph and let $G_\alpha$, $G_\omega$ be the section hypergraphs of $G$ induced by $V_\alpha,V_\omega\subseteq V$, with $G_\alpha\cup G_\omega=G$, i.e. $V_\alpha\cup V_\omega=V$ and $E(G_\alpha)\cup E(G_\omega)=E$. Let $\bar p=V_\alpha\cap V_\omega$ and suppose that $\bar p$ is a node of $G$ or an edge of $G$, and that $G_\alpha$ is two-laminar and β-acyclic. Then $\mathcal S_G$ is decomposable into $\mathcal S_{G_\alpha}$ and $\mathcal S_{G_\omega}$:
--   $$\operatorname{conv}\mathcal S_G=\operatorname{conv}\bar{\mathcal S}_{G_\alpha}\cap\operatorname{conv}\bar{\mathcal S}_{G_\omega},$$
--   where $\bar{\mathcal S}_{G_\alpha}$ (resp. $\bar{\mathcal S}_{G_\omega}$) is the set of points of the space of $\mathcal S_G$ whose projection onto the space of $G_\alpha$ (resp. $G_\omega$) lies in $\mathcal S_{G_\alpha}$ (resp. $\mathcal S_{G_\omega}$).
--
--   This decomposition theorem is what allows the multilinear polytope of a kite-free β-acyclic hypergraph to be glued from the polytopes of two-laminar pieces.
--
--   **Formalization Note** "$\bar p\in V(G)\cup E(G)$" is encoded as: $V_\alpha\cap V_\omega$ has exactly one element (a node, read as its singleton) or is an edge of $G$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1022, Theorem 1 (decomposability as defined in §3.3.2, p. 1021)

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem theorem_1 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (Wa Wo : Finset α)
    (hWa : Wa ⊆ G.V) (hWo : Wo ⊆ G.V) (hV : Wa ∪ Wo = G.V)
    (hE : (sectionHg G Wa).E ∪ (sectionHg G Wo).E = G.E)
    (hp : (Wa ∩ Wo).card = 1 ∨ Wa ∩ Wo ∈ G.E)
    (hlam : IsLaminar (sectionHg G Wa) 2) (hβ : IsBetaAcyclic (sectionHg G Wa)) :
    MP G = convexHull ℝ (SBar G (sectionHg G Wa)) ∩ convexHull ℝ (SBar G (sectionHg G Wo)) := by sorry

end RunIntersect.Tight
