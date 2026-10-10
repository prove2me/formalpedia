-- Prove2me | Theorems.Thm_RunIntersect_Tight_claim_14
-- name    : RunIntersect.Tight.claim_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:36.316553+00:00
-- url     : https://prove2.me/theorems/5dc51db3-bcb2-48a9-8bc9-1ab369846677
-- title:
--   Claim 14, p. 1035 — every inequality defining MP^RI of a partial hypergraph G′ is present in the system defining MP^RI_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph and $G'=(V',E')$ a partial hypergraph of $G$ ($V'\subseteq V$, $E'\subseteq E$). Then all inequalities defining $\mathrm{MP}^{\mathrm{RI}}_{G'}$ are also present in the system defining $\mathrm{MP}^{\mathrm{RI}}_G$:
--
--   1. every running intersection inequality of $G'$ is, with the same left-hand side and the same right-hand side, a running intersection inequality of $G$;
--   2. consequently, for every $z\in\mathrm{MP}^{\mathrm{RI}}_G$, the projection of $z$ onto the space of $G'$ lies in $\mathrm{MP}^{\mathrm{RI}}_{G'}$ (this also covers the rows of the standard linearization (8) of $G'$, which are rows of (8) for $G$).
--
--   The claim is used in the Fourier–Motzkin step of the proof of Theorem 3, to recognise projected inequalities as inequalities of $\mathrm{MP}^{\mathrm{RI}}_G$.
--
--   **Formalization Note** The rows of (8) are indexed by nodes and edges, so "present in the system" for them is the inclusion $V'\subseteq V$, $E'\subseteq E$ itself; it is expressed through the second conjunct, on points.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1035, Claim 14 (§5.3.2)

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem claim_14 {α : Type*} [Fintype α] [DecidableEq α] (G G' : Hypergraph α) (hV : G'.V ⊆ G.V) (hE : G'.E ⊆ G.E) :
    (∀ d' : RIData G', ∃ d : RIData G, d.lhs = d'.lhs ∧ d.rhs = d'.rhs) ∧
      ∀ z ∈ MPRI G, restrict G' z ∈ MPRI G' := by sorry

end RunIntersect.Tight
