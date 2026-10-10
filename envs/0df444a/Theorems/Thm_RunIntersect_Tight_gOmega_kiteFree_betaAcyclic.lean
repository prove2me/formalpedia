-- Prove2me | Theorems.Thm_RunIntersect_Tight_gOmega_kiteFree_betaAcyclic
-- name    : RunIntersect.Tight.gOmega_kiteFree_betaAcyclic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:07.143832+00:00
-- url     : https://prove2.me/theorems/159a7e23-96cf-4454-9074-5ea424d90226
-- title:
--   §5.3.1, p. 1035 — G_ω has κ − 1 maximal edges and is kite-free β-acyclic
-- statement:
--   Let $G=(V,E)$ be a kite-free β-acyclic hypergraph with $\kappa\ge 2$ maximal edges, and let $\mathcal O=\bar e_1,\dots,\bar e_\kappa$ be a running intersection ordering of its maximal edges. Let $\tilde e=\bar e_\kappa$ be the last one and $\bar p=N(\tilde e)=\tilde e\cap\bigcup_{j<\kappa}\bar e_j$. Let $G^+$ be $G$ with $\bar p$ added as an edge when $|\bar p|\ge 2$; let $G_\alpha$ be the section hypergraph of $G^+$ induced by $\tilde e$, and $G_\omega$ the section hypergraph of $G^+$ induced by $\bigcup_{e\in E(G^+)\setminus E(G_\alpha)}e$. Then
--
--   1. $G_\omega$ is kite-free;
--   2. $G_\omega$ is β-acyclic;
--   3. $G_\omega$ has exactly $\kappa-1$ maximal edges.
--
--   This is the step of the proof of Theorem 3 that makes the induction hypothesis applicable to $G_\omega$.
--
--   **Formalization Note** The ordering is a duplicate-free list `O` whose set of elements is the set of maximal edges and which satisfies (2); $\tilde e$ is its last element and $\bar p$ the set (3) at the last position. The page adds $\bar p$ "if $\bar p\notin V\cup E$"; the Lean adds it when $|\bar p|\ge 2$, which is the same when $|\bar p|\ge 1$, and avoids adding the empty set when $\tilde e$ meets no other maximal edge. The page writes "the section hypergraph of $G$ induced by …" for $G_\omega$; it must be $G^+$ ($\bar p$ is an edge of $G_\omega$ two sentences later), and the Lean uses $G^+$. No hypothesis on isolated nodes is needed for this combinatorial statement.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1035, §5.3.1 (proof of Theorem 3), second paragraph

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem gOmega_kiteFree_betaAcyclic {α : Type*} [Fintype α] [DecidableEq α]
    (G : Hypergraph α) (hkite : IsKiteFree G) (hβ : IsBetaAcyclic G)
    (O : List (Finset α)) (hOnd : O.Nodup) (hO : O.toFinset = maxEdges G) (hOri : IsRIOrder O)
    (hκ : 2 ≤ O.length) :
    IsKiteFree (GOmega G O) ∧ IsBetaAcyclic (GOmega G O) ∧
      (maxEdges (GOmega G O)).card = O.length - 1 := by sorry

end RunIntersect.Tight
