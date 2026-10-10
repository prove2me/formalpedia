-- Prove2me | Theorems.Thm_RunIntersect_Tight_proposition_6
-- name    : RunIntersect.Tight.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:01.330903+00:00
-- url     : https://prove2.me/theorems/e22e7b13-0b96-4814-8c3e-d8f648687f9d
-- title:
--   Proposition 6, p. 1021 — for a two-laminar β-acyclic hypergraph, MP_G is described by system (20)
-- statement:
--   Let $G=(V,E)$ be a two-laminar β-acyclic hypergraph. For $e\in E$ let $I(e)$ be the set of nodes and edges $p$ with $p\subset e$ that are strictly contained in no edge $e'\in E$ with $e'\subset e$; let $\omega(e)$ be the number of connected components of $H_e=(e,I(e)\cap E)$, and $\delta_e(v)$ the number of edges of $H_e$ containing $v$. Then $\mathrm{MP}_G$ is described by the system
--   $$\begin{aligned}
--   z_v&\le 1 &&\forall v\in V,\\
--   -z_p&\le 0 &&\forall p\in V\cup E \text{ with } p\not\subset f \text{ for every } f\in E,\\
--   -z_p+z_e&\le 0 &&\forall e\in E,\ \forall p\in I(e),\\
--   \sum_{v\in e}(1-\delta_e(v))z_v+\sum_{p\in I(e)\cap E}z_p-z_e&\le \omega(e)-1 &&\forall e\in E.
--   \end{aligned}$$
--
--   This explicit facet description (with general integer coefficients) is the base case of the paper's characterization; each of its inequalities is a row of (8) or a running intersection inequality, which gives Corollary 3.
--
--   **Formalization Note** "$p\not\subset f$ for every $f\in E$" is read with strict inclusion: for a node, it lies in no edge; for an edge, it is maximal. No hypothesis on isolated nodes is needed here, because the second family bounds $z_v$ below for every node in no edge.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1021, Proposition 6, system (20)

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem proposition_6 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (hlam : IsLaminar G 2)
    (hβ : IsBetaAcyclic G) :
    MP G = system20 G := by sorry

end RunIntersect.Tight
