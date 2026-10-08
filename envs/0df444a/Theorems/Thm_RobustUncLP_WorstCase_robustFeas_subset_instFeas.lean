-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_robustFeas_subset_instFeas
-- name    : RobustUncLP.WorstCase.robustFeas_subset_instFeas
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:51:35.14666+00:00
-- url     : https://prove2.me/theorems/e769553f-ebc0-4722-b7f3-ee175715cd67
-- title:
--   §2.2, proof of Proposition 2.1(i), p. 5 — the feasible set of (P_𝒰) is contained in that of every instance
-- statement:
--   Let $\mathcal U$ be a set of real $m\times n$ matrices and $f\in\mathbb R^{n}$. For every $A \in \mathcal U$,
--   $$G_{\mathcal U} = \{x \mid Bx \ge 0\ \forall B\in\mathcal U;\ f^{T}x = 1\} \ \subseteq\ \{x \mid Ax \ge 0,\ f^{T}x = 1\}.$$
--
--   This is the "if" part of Proposition 2.1(i): an infeasible instance makes the robust counterpart infeasible.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, §2.2, proof of Proposition 2.1, first sentence

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem robustFeas_subset_instFeas {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) :
    ∀ A ∈ U, robustFeas U f ⊆ instFeas f A := by sorry

end RobustUncLP.WorstCase
