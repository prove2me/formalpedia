-- Prove2me | Theorems.Thm_RobustUncLP_Ellipsoidal_P_strictly_feasible_bddBelow
-- name    : RobustUncLP.Ellipsoidal.P_strictly_feasible_bddBelow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:30:04.600572+00:00
-- url     : https://prove2.me/theorems/b62fbe73-710c-4cc6-bcdb-5ce4319f9158
-- title:
--   Appendix, p. 16 — under B and C each (P_i[x]) is strictly feasible and bounded below
-- statement:
--   Let $\mathcal U = \bigcap_{\ell=0}^k U(\Pi_\ell, Q_\ell)$ satisfy condition B ($\mathcal U$ bounded) and condition C (some $A$ equals $\Pi_\ell(u^\ell)$ with $\|Q_\ell u^\ell\| < 1$ for every $\ell = 0,\dots,k$). Then:
--
--   1. the problems $(P_i[x])$ are strictly feasible: there is $(u^0,\dots,u^k)$ with $\Pi_\ell(u^\ell) = \Pi_0(u^0)$ and $\|Q_\ell u^\ell\| < 1$ for all $\ell$;
--   2. for every $x \in \mathbb R^n$ and every row $i$, the objective $a_i[\Pi_0(u^0)]^Tx$ is bounded below on the feasible set of $(P_i[x])$.
--
--   These are exactly the hypotheses under which (II) applies to $(P_i[x])$.
--
--   **Formalization Note** Boundedness of $\mathcal U$ is a uniform bound on all matrix entries (`UncBounded`). Condition C is read for every $\ell = 0, \dots, k$ (see the `Setting` definition).
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, Appendix, p. 16, first sentence

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

namespace RobustUncLP.Ellipsoidal

open Matrix EllipsoidalData

/-- Appendix, p. 16: under conditions B and C, every problem `(P_i[x])` is strictly feasible and
its objective is bounded below on its feasible set. -/
theorem P_strictly_feasible_bddBelow {m n k : ℕ} (D : EllipsoidalData m n k)
    (hB : UncBounded D.uncSet) (hC : D.SlaterC) :
    (∃ u ∈ PFeas D, ∀ ℓ, euclidNorm (D.Q ℓ *ᵥ u ℓ) < 1) ∧
      ∀ (x : Fin n → ℝ) (i : Fin m),
        BddBelow ((fun u => (D.Pi 0 (u 0) *ᵥ x) i) '' PFeas D) := by sorry

end RobustUncLP.Ellipsoidal
