-- Prove2me | Theorems.Thm_SuperBAE_Restriction_lift_either
-- name    : SuperBAE.Restriction.lift_either
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:37.772498+00:00
-- url     : https://prove2.me/theorems/ed0b260f-d999-420b-96e3-ca8cf8fe2c0a
-- title:
--   §4.2, p. 19 (PDF 20) — lift: given a reduced solution and R1, it suffices to solve either (4.2) or (4.4)
-- statement:
--   In the setting of the $\mathfrak{gl}(M|N)$ Bethe ansatz equations (2.9) with $n=M-N>0$, let $\alpha_k$ satisfy **A1** ($\sigma_k\sigma_{k+1}=-1$) and **A2** ($2\le k\le d-2$), assume **R1** (the roots of types $k-1$ and $k+1$ coincide) and that the root family is regular. Suppose the reduced root family (types $k,k+1$ deleted) solves the reduced $\mathfrak{gl}(M-1|N-1)$ Bethe ansatz equations for the deleted grading. Then for every root $u$ of type $k-1$,
--   $$(4.2)\text{ at }u \iff (4.4)\text{ at }u .$$
--
--   This is the first step of the lift in §4.2: once the roots of type $k+1$ are defined to be those of type $k-1$, finding the roots of type $k$ amounts to solving either (4.2) or (4.4).
--
--   **Formalization Note.** Regularity is added; it makes the sides of (4.2) nonzero so that (4.4) can be recovered from (4.6) by division. Existence of the type-$k$ roots (for $p = \nu^{(k)} \ge P$) and the uniqueness claim of §4.2 are not part of this statement. The standing assumption $N<M$ (p. 7) is kept; it is not used.
-- source:
--   Candu, Continuum Limit of gl(M|N) Spin Chains, arXiv:1012.0050v1, p. 19 (PDF 20), §4.2, "the task is reduced to finding a solution … to either eq. (4.2) or eq. (4.4)"

import Mathlib
import Definitions.Def_SuperBAE_Restriction_Model

namespace SuperBAE.Restriction

theorem lift_either (L : ℕ) (odd : ℕ → Bool) (d : ℕ) (roots : ℕ → Finset ℂ) (k : ℕ)
    (hA1 : odd k ≠ odd (k + 1)) (hA2k : 2 ≤ k) (hA2d : k + 2 ≤ d)
    (hn : numOdd odd d < numEven odd d)
    (hR1 : roots (k - 1) = roots (k + 1)) (hreg : Regular L odd d roots)
    (hred : IsBAESolution L (delGrading k odd) (d - 2) (delRoots k roots)) :
    ∀ u ∈ roots (k - 1), eq4_2 L odd d roots k u ↔ eq4_4 L odd d roots k u := by sorry

end SuperBAE.Restriction
