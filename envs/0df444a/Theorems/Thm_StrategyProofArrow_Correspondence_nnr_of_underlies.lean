-- Prove2me | Theorems.Thm_StrategyProofArrow_Correspondence_nnr_of_underlies
-- name    : StrategyProofArrow.Correspondence.nnr_of_underlies
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:04.466827+00:00
-- url     : https://prove2.me/theorems/9a27edc1-0327-44c2-81ca-65074ebf3148
-- title:
--   §4, p. 34 — a strict SWF with PO and IIA underlying a strategy-proof procedure satisfies NNR
-- statement:
--   Let $n\ge2$, $m\ge3$, let $v:\rho_m^n\to S_m$ be a strict strategy-proof voting procedure, and let $u:\rho_m^n\to\rho_m$ be a strict social welfare function that underlies $v$ and satisfies Pareto optimality and IIA. Then $u$ satisfies non-negative response: for every alternative $x$, with $W=S_m\setminus\{x\}$, and all strict ballot sets $C,D$ such that, for every individual $i$, $\theta_W(C_i)=\theta_W(D_i)$ and $x$ is ranked by $D_i$ at least as high against every $y\in W$ as by $C_i$,
--   $$x\,\bar A_C\,z\ \Longrightarrow\ x\,\bar A_D\,z\qquad\text{for all } z\in W,$$
--   where $A_C=u(C)$ and $A_D=u(D)$.
--
--   This is the paper's "third fact" about Gibbard's result, which completes the proof of Lemma 8.
--
--   **Formalization Note** NNR is formalized for every $x$ and for arbitrary $C,D$ (any number of individuals may move $x$ up); the paper's argument treats a change in a single ballot. The standing hypotheses $n\ge2$, $m\ge3$ of §4 are kept.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §4, p. 34 ("Third, note that …")

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

namespace StrategyProofArrow.Correspondence

theorem nnr_of_underlies {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι] [DecidableEq A]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (v : StrongProfile ι A → A) (hsp : StrategyProof v)
    (u : StrongProfile ι A → StrongOrder A) (hu : Underlies u v) (hpo : PO u) (hiia : IIA u) :
    NNR u := by sorry

end StrategyProofArrow.Correspondence
