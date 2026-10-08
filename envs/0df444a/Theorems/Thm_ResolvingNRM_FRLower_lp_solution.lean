-- Prove2me | Theorems.Thm_ResolvingNRM_FRLower_lp_solution
-- name    : ResolvingNRM.FRLower.lp_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:41:30.453557+00:00
-- url     : https://prove2.me/theorems/36d260c2-9720-4404-8651-a904542a27fd
-- title:
--   Appendix D, p. 42 — optimal DLP allocation on the two-class instance
-- statement:
--   Let $0<r_2<r_1$ and consider the two-class instance with one unit of resource consumed by either accepted customer. For any nonnegative average resource capacity $b$, every optimal DLP allocation $x=(x_1,x_2)$ satisfies
--
--   $$
--   x_1=\min\{b,1\},\qquad x_2=\min\{\max\{b-1,0\},1\}.
--   $$
--
--   The first coordinate is the admission probability for class 1 used in the paper's phase-two argument; the second determines the class-2 admission probability when capacity exceeds one.
--
--   **Formalization Note** The page states the $x_1$ formula explicitly; the $x_2$ formula is the unique optimal companion under $0<r_2<r_1$ and is used implicitly in (64)–(65). Nonnegative $b$ is the domain of the policy's LP.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Appendix D, p. 42, paragraph before (61) and (64)–(65)

import Mathlib
import Definitions.Def_ResolvingNRM_FRLower_Instance

namespace ResolvingNRM.FRLower

/-- The unique optimal DLP allocation of the two-class instance. The first equality is
stated on p. 42; the second is the implicit companion used in (64)–(65). -/
theorem lp_solution (r₁ r₂ : ℝ) (hr₂ : 0 < r₂) (hr : r₂ < r₁)
    (b : Fin 1 → ℝ) (hb : 0 ≤ b 0) (x : Fin 2 → ℝ)
    (hx : IsDLPOptimal (twoClass r₁ r₂ (le_of_lt hr₂) (le_of_lt hr)) b x) :
    x 0 = min (b 0) 1 ∧ x 1 = min (max (b 0 - 1) 0) 1 := by sorry

end ResolvingNRM.FRLower
