-- Prove2me | Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
-- name    : ValuationSubring.isAlgClosed_completion_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/5c76664b-353c-5508-b107-424830eb6fdb
-- title:
--   Completion of ℚ̄ at a place above p is algebraically closed
-- statement:
--   Let $p$ be a natural number, assumed prime, and let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$. Assume that $A$ satisfies `LiesOverPrime p`, which by definition says that the image of $p$ in $\overline{\mathbb{Q}}$ lies in the set of non-units of $A$, i.e. $p$ belongs to the maximal ideal of $A$ (equivalently $v_A(p) < 1$ for the associated valuation $v_A$ of $A$, with values in its value group). The conclusion is that the completion of $\overline{\mathbb{Q}}$ with respect to the valuation $v_A$ attached to $A$ — the field `A.valuation.Completion` — is algebraically closed. Thus for every place of $\overline{\mathbb{Q}}$ lying above the rational prime $p$, the corresponding completion is an algebraically closed field; it is a model of $\mathbb{C}_p$ attached to that place.
--
--   This is the classical fact, going back to Kürschák, that the completion of an algebraically closed field at a rank-one non-archimedean place remains algebraically closed, specialised to the places of $\overline{\mathbb{Q}}$ above a prime $p$; it provides the coefficient field $\mathbb{C}_p$ used throughout the $p$-adic analytic parts of the development, in particular in the construction of Picard groups and theta functions for Mumford quotients of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.isAlgClosed_completion_of_liesOverPrime
    (p : ℕ) (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    IsAlgClosed A.valuation.Completion := by sorry
