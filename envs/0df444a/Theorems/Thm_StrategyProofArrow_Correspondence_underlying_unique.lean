-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_underlying_unique
-- name    : StrategyProofArrow.Correspondence.underlying_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:00.101531+00:00
-- url     : https://prove2.me/theorems/840c4587-c15f-4b5d-906b-a4b0ca3f3701
-- title:
--   §4, p. 34 — at most one strict SWF with PO and IIA underlies a strict strategy-proof voting procedure
-- statement:
--   Let $n\ge2$, $m\ge3$, and let $v:\rho_m^n\to S_m$ be a strict strategy-proof voting procedure. If two strict social welfare functions $\mu,\mu':\rho_m^n\to\rho_m$ both underlie $v$ and both satisfy Pareto optimality and independence of irrelevant alternatives, then
--   $$\mu=\mu',$$
--   that is, $\mu(B)=\mu'(B)$ for every strict ballot set $B$.
--
--   This is the paper's "second fact" about Gibbard's result, the uniqueness half of Lemma 8.
--
--   **Formalization Note** Equality is equality of functions on strict ballot sets, which is the paper's equality because the domain is exactly $\rho_m^n$ (a subtype). The standing hypotheses $n\ge2$, $m\ge3$ of §4 are kept; the range condition is not assumed, since the paper's argument does not use it.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §4, p. 34 ("The second fact …")

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem underlying_unique {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v)
    (u u' : StrongProfile ι A → StrongOrder A)
    (hu : Underlies u v) (hpo : PO u) (hiia : IIA u)
    (hu' : Underlies u' v) (hpo' : PO u') (hiia' : IIA u') :
    u = u' := by sorry

end StrategyProofArrow.Correspondence
