-- Prove2me | Theorems.Thm_RunIntersect_Strict_lemma_6
-- name    : RunIntersect.Strict.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:37:26.311902+00:00
-- url     : https://prove2.me/theorems/9f55dff9-efa5-4394-88c8-3fcb5c9df462
-- title:
--   Lemma 6, p. 1019 — MP^RI_{G_V̄} ⊆ proj_{G_V̄}(MP^RI_G ∩ L_V̄) when G_V̄ has no isolated node
-- statement:
--   Let $G=(V,E)$ be a hypergraph, $\bar V\subseteq V$, $L_{\bar V}$ as in (18), and $\mathrm{proj}_{G_{\bar V}}$ the projection defined by any choice of edges $e'(f)\in E$ with $e'(f)\cap\bar V=f$ for the edges $f$ of $G_{\bar V}$. Assume that the subhypergraph $G_{\bar V}$ has no isolated node. Then
--   $$\mathrm{MP}^{\mathrm{RI}}_{G_{\bar V}}\subseteq\mathrm{proj}_{G_{\bar V}}\big(\mathrm{MP}^{\mathrm{RI}}_G\cap L_{\bar V}\big).$$
--
--   This is the weaker analogue of Lemma 5 for the running intersection relaxation; together they reduce strictness of $\mathrm{MP}_G\subset\mathrm{MP}^{\mathrm{RI}}_G$ to strictness for an induced subhypergraph.
--
--   **Formalization Note** The page prints $\mathrm{MP}^{RI}_{G_V}$ and $L_V$, with the bars lost; the statement here is the barred one (the unbarred $G_V$ is $G$ itself). The hypothesis that $G_{\bar V}$ has no isolated node is added: (8) has no lower bound $z_v\ge 0$, so a node $v$ isolated in $G_{\bar V}$ is unbounded below in $\mathrm{MP}^{\mathrm{RI}}_{G_{\bar V}}$, while if $v$ lies in an edge $e$ of $G$ every point of $\mathrm{MP}^{\mathrm{RI}}_G$ has $z_v\ge z_e\ge 0$. For example $V=\{a,b\}$, $E=\{\{a,b\}\}$, $\bar V=\{a\}$: the point $z_a=-1$ is in $\mathrm{MP}^{\mathrm{RI}}_{G_{\bar V}}$ and not in the projection. In the paper the lemma is applied only with $\bar V=V(C)$ for a β-cycle $C$, where $G_{\bar V}$ has no isolated node.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, Lemma 6 (stated without proof; printed G_V, L_V read as G_V̄, L_V̄)

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Lemma 6, p. 1019 (the page prints `G_V`, `L_V` for `G_{V̄}`, `L_{V̄}`):
`MP^RI_{G_W} ⊆ proj_{G_W}(MP^RI_G ∩ L_W)`, for every choice `ep` of the edges `e′(f)`.
Added hypothesis: `G_W` has no isolated node (without it the statement is false, see the note). -/
theorem lemma_6 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (W : Finset α)
    (hW : W ⊆ G.V) (hiso : NoIsolated (subHg G W)) (ep : Finset α → Finset α)
    (hep : ∀ f ∈ (subHg G W).E, ep f ∈ G.E ∧ ep f ∩ W = f) :
    MPRI (subHg G W) ⊆ projSub G W ep '' (MPRI G ∩ Lset G W) := by sorry

end RunIntersect.Strict
