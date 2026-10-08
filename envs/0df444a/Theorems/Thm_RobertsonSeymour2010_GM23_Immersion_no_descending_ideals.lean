-- Prove2me | Theorems.Thm_RobertsonSeymour2010_GM23_Immersion_no_descending_ideals
-- name    : RobertsonSeymour2010.GM23.Immersion.no_descending_ideals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:25.124123+00:00
-- url     : https://prove2.me/theorems/d2408ca4-faa4-4f0b-b80b-db54309445a9
-- title:
--   3.1 — no infinite strictly descending chain of ideals below a well-quasi-order
-- statement:
--   Let $\Omega_1,\Omega_2,\dots$ be quasi-orders on subsets of a common ambient set. Write $\Omega<\Omega'$ when $\Omega$ is an ideal of $\Omega'$ (a sub-quasi-order closed downwards in $\Omega'$) and $\Omega\ne\Omega'$. Then there is no sequence such that $\Omega_1$ is a well-quasi-order and
--   $$\Omega_{i+1}<\Omega_i\qquad\text{for all } i\ge1 .$$
--
--   In other words, the relation "is a proper ideal of" is well-founded below any well-quasi-order. The paper calls this a well-known lemma and uses it, through 3.2, to run an induction on shadows.
--
--   **Formalization Note.** Quasi-orders are `QO X` on a common ambient type `X`; the sequence is indexed from $0$, so the paper's $\Omega_1$ is `Ω 0`. "$\Omega\ne\Omega'$" is the negation of `QO.Same` (same ground set and same order on it).
-- source:
--   Robertson, Seymour, Graph Minors XXIII. Nash-Williams' immersion conjecture (authors' manuscript, rev. Apr. 18, 2011), 3.1, p. 6

import Mathlib
import Definitions.Def_RobertsonSeymour2010_GM23_Immersion_QuasiOrders

namespace RobertsonSeymour2010.GM23.Immersion

theorem no_descending_ideals (X : Type) (Ω : ℕ → QO X) (hΩ : (Ω 0).IsWQO) :
    ¬ ∀ i : ℕ, (Ω (i + 1)).IsProperIdeal (Ω i) := by sorry

end RobertsonSeymour2010.GM23.Immersion
