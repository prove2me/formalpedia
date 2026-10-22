-- Prove2me | Theorems.Thm_WalledBrauer_Center_proposition_1_1
-- name    : WalledBrauer.Center.proposition_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:28.824988+00:00
-- url     : https://prove2.me/theorems/5ea02365-8bd6-4734-b246-caa8ff681d52
-- title:
--   Proposition 1.1 ([3, Theorem 6.3]) — when $B_{r,s}(\delta)$ is semisimple
-- statement:
--   The walled Brauer algebra $B_{r,s}(\delta)$ over $\mathbb C$ is semisimple if and only if one of the following holds:
--
--   1. $r=0$ or $s=0$;
--   2. $\delta\notin\mathbb Z$;
--   3. $|\delta|>r+s-2$;
--   4. $\delta=0$ and $(r,s)\in\{(1,2),(1,3),(2,1),(3,1)\}$.
--
--   In particular, for fixed $(r,s)$ the algebra is semisimple for all but finitely many $\delta$. This criterion, due to Cox, De Visscher, Doty and Martin, is the setting in which the main theorem of Jung and Kim applies, and it is used in the proof of Lemma 2.12.
--
--   **Formalization Note** Semisimplicity is Mathlib's `IsSemisimpleRing`. $|\delta|$ is the complex modulus `‖δ‖`, and $r+s-2$ is computed in $\mathbb R$, so that it is negative when $r+s<2$ (no natural-number truncation). $\delta\notin\mathbb Z$ means $\delta$ is not the image of an integer. Semisimplicity does not depend on the product convention (a ring is semisimple iff its opposite is).
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 6, Proposition 1.1 (citing Cox–De Visscher–Doty–Martin, Theorem 6.3)

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem proposition_1_1 (r s : ℕ) (δ : ℂ) :
    IsSemisimpleRing (B r s δ) ↔
      (r = 0 ∨ s = 0) ∨
      δ ∉ Set.range (Int.cast : ℤ → ℂ) ∨
      ((r : ℝ) + (s : ℝ) - 2 < ‖δ‖) ∨
      (δ = 0 ∧ (r, s) ∈ ({(1, 2), (1, 3), (2, 1), (3, 1)} : Finset (ℕ × ℕ))) := by sorry
end WalledBrauer.Center
