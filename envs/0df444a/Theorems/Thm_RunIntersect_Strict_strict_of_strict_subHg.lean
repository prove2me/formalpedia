-- Prove2me | Theorems.Thm_RunIntersect_Strict_strict_of_strict_subHg
-- name    : RunIntersect.Strict.strict_of_strict_subHg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:33.566264+00:00
-- url     : https://prove2.me/theorems/4847c2ec-4ba2-4056-a985-ae51afb72d88
-- title:
--   Proof of Proposition 5, p. 1019 — by Lemmas 5 and 6, MP_{G_W} ⊂ MP^RI_{G_W} implies MP_G ⊂ MP^RI_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph and $W\subseteq V$ such that the subhypergraph $G_W$ has no isolated node. Then
--   $$\mathrm{MP}_{G_W}\subsetneq\mathrm{MP}^{\mathrm{RI}}_{G_W}\ \Longrightarrow\ \mathrm{MP}_G\subsetneq\mathrm{MP}^{\mathrm{RI}}_G .$$
--
--   This is the reduction step of the proof of Proposition 5: a gap between the multilinear polytope and the running intersection relaxation of an induced subhypergraph lifts to the whole hypergraph.
--
--   **Formalization Note** The hypothesis that $G_W$ has no isolated node is added for the reason given at Lemma 6, and is necessary: for $V=\{a,b\}$, $E=\{\{a,b\}\}$, $W=\{a\}$ one has $\mathrm{MP}_{G_W}=[0,1]\subsetneq(-\infty,1]=\mathrm{MP}^{\mathrm{RI}}_{G_W}$, while $\mathrm{MP}_G=\mathrm{MP}^{\mathrm{RI}}_G$ for a single edge. The paper applies the step with $W=V(C)$, which has no isolated node.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, proof of Proposition 5, first paragraph

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Proof of Proposition 5, p. 1019: by Lemmas 5 and 6, `MP_{G_W} ⊂ MP^RI_{G_W}` implies
`MP_G ⊂ MP^RI_G`. Added hypothesis: `G_W` has no isolated node (true for `W = V(C)`). -/
theorem strict_of_strict_subHg {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α)
    (W : Finset α) (hW : W ⊆ G.V) (hiso : NoIsolated (subHg G W)) :
    MP (subHg G W) ⊂ MPRI (subHg G W) → MP G ⊂ MPRI G := by sorry

end RunIntersect.Strict
