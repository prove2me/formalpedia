-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_lagrangean_bound_valid_for_P
-- name    : RossSolandGAP.Bound.lagrangean_bound_valid_for_P
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:09:12.658995+00:00
-- url     : https://prove2.me/theorems/d68566d1-7941-4d7b-aa84-fdd241762acb
-- title:
--   §2, p. 95 — any lower bound on (PR_λ) is a lower bound for (P)
-- statement:
--   Fix multipliers $\lambda_j\in\mathbb R$, one for each assignment constraint $\sum_{i}x_{ij}=1$. The Lagrangean relaxation is
--
--   $$
--   \text{(PR}_\lambda)\qquad \min\ \sum_{i\in I}\sum_{j\in J}c_{ij}x_{ij}+\sum_{j\in J}\lambda_j\Bigl(1-\sum_{i\in I}x_{ij}\Bigr)\quad\text{s.t.}\quad \sum_{j\in J}r_{ij}x_{ij}\le b_i\ (i\in I),\ x_{ij}\in\{0,1\}.
--   $$
--
--   Every $x$ feasible for (P) is feasible for (PR$_\lambda$), and there its (PR$_\lambda$) objective equals its (P) objective. Hence, if a real number $L$ satisfies $L\le$ the (PR$_\lambda$) objective of every (PR$_\lambda$)-feasible $x$, then $L\le\sum_i\sum_j c_{ij}x_{ij}$ for every $x$ feasible for (P).
--
--   This is why the bound "provided by (PR$_\lambda$)" is a valid bound for (P), whatever the multipliers.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, p. 95, §2, first two paragraphs and (PR_λ); p. 96, second paragraph, last sentence

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem lagrangean_bound_valid_for_P {m n : ℕ} (c r : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (lam : Fin n → ℝ) :
    (∀ x, FeasibleP r b x → FeasibleLag r b x ∧ lagObj c lam x = cost c x) ∧
    ∀ L : ℝ, (∀ x, FeasibleLag r b x → L ≤ lagObj c lam x) →
      ∀ x, FeasibleP r b x → L ≤ cost c x := by sorry

end RossSolandGAP.Bound
