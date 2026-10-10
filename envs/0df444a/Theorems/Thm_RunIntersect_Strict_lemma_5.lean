-- Prove2me | Theorems.Thm_RunIntersect_Strict_lemma_5
-- name    : RunIntersect.Strict.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:37.305541+00:00
-- url     : https://prove2.me/theorems/3f1e2d39-c4ef-4e2f-8e4f-4ed9c23c7f83
-- title:
--   Lemma 5, p. 1019 — MP_{G_V̄} = proj_{G_V̄}(MP_G ∩ L_V̄)
-- statement:
--   Let $G=(V,E)$ be a hypergraph, $\bar V\subseteq V$, and $L_{\bar V}=\{z: z_v=1\ \forall v\in V\setminus\bar V\}$ as in (18). For every edge $f$ of the subhypergraph $G_{\bar V}$ fix any edge $e'(f)\in E$ with $e'(f)\cap\bar V=f$, and let $\mathrm{proj}_{G_{\bar V}}$ keep the variables $z_v$, $v\in\bar V$, read the variable of $f$ from $z_{e'(f)}$, and project out all other variables. Then
--   $$\mathrm{MP}_{G_{\bar V}}=\mathrm{proj}_{G_{\bar V}}\big(\mathrm{MP}_G\cap L_{\bar V}\big).$$
--
--   The statement holds for every choice of the edges $e'(f)$. It shows that the multilinear polytope of an induced subhypergraph is a projection of a face of $\mathrm{MP}_G$, which is what lets a gap between $\mathrm{MP}$ and a relaxation be transferred from $G_{\bar V}$ to $G$.
--
--   **Formalization Note** The paper quotes this result from Del Pia and Khajavirad (2018). The choice $e'$ is a hypothesis-carrying argument `ep`, so the lemma is stated for every choice.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, Lemma 5 ((18) and the definition of proj on the same page; e′(e) on p. 1018)

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Lemma 5, p. 1019: `MP_{G_W} = proj_{G_W}(MP_G ∩ L_W)`, for every choice `ep` of the edges `e′(f)`. -/
theorem lemma_5 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (W : Finset α)
    (hW : W ⊆ G.V) (ep : Finset α → Finset α)
    (hep : ∀ f ∈ (subHg G W).E, ep f ∈ G.E ∧ ep f ∩ W = f) :
    MP (subHg G W) = projSub G W ep '' (MP G ∩ Lset G W) := by sorry

end RunIntersect.Strict
