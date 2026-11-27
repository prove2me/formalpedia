-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_Supplement_theorem_3_2_counterexample
-- name    : RetirePartialInfo.Duality.Supplement.theorem_3_2_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:23:06.38309+00:00
-- url     : https://prove2.me/theorems/31daa355-6847-4728-80fa-5bb4c2509e70
-- title:
--   Theorem 3.2 (corrected: zero-income counterexample to global Sobolev existence)
-- statement:
--   The source allows zero labour income. For every admissible HMM with $\xi=0$, $T_1>0$ and finite $q\ge1$, the complete printed existence package is impossible:
--
--   $$\neg\exists f\in W_q^{1,2,2}(\mathcal M_{T_1})\cap C^1(\overline{\mathcal M}_{T_1}):\ (32),\quad g^+\le f\le\frac\ell\beta(1-e^{-\beta(T_1-t)})+2,\quad -\frac\xi r(1-e^{-r(T_1-t)})\le f_y\le0,\quad f_p\ge0.$$
--
--   The exact additive constant 2 and unconditional belief monotonicity are retained inside the negation. When $\xi=0$, $g=\ell(1-e^{-\beta(T_1-t)})/\beta$ is strictly positive for $t<T_1$ and independent of $y$, contradicting the zeroth-order global $L^q$ requirement. The same concrete HMM parameters as in the preceding counterexample are allowed. This diagnoses the global claim without choosing a bounded multiplier domain or changing its function space.
--
--   **Formalization Note** VI derivatives are genuine weak derivatives and the equation holds almost everywhere; the counterexample already follows from its pointwise lower estimate.
--
--   Differences from the source:
--   - correction: Existence of a global W_q VI solution with (37)–(39) → Negation of the whole existence package for ξ=0 and T1>0; reason: The permitted zero-income case makes g+ positive independently of y, so (37) precludes global L^q; see DISPROOF.md
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 20, Theorem 3.2, (37)–(39); p. 16, definition of W_q; p. 17, (32)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Analysis

open Set
set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), p.20, Theorem 3.2, (37)–(39); p.17, (32).
**Formalization Note.** Counterexample on the source-allowed ξ=0 subfamily, T1>0.
Then g(t,y)=ℓ(1-exp(-β(T1-t)))/β>0 for t<T1, independent of y and p.
Thus (37) contradicts global L^q on the unbounded y-domain. Every clause of the printed
existence package, including +2 and unconditional p monotonicity, is inside the negation.
No sign condition is imposed on the risk premium; no replacement with a local space. -/
theorem theorem_3_2_counterexample (a : Data) (ha : a.Admissible)
    (hxi : a.par.ξ = 0) (hh : 0 < a.par.T1) (q : ℝ) (hq : 1 ≤ q) :
    ¬ ∃ f : Value,
      GlobalW a.par.T1 q f ∧ C1 a.par.T1 f ∧ VI32 a f ∧
      (∀ z ∈ domain a.par.T1,
        max (obstacle a (z 0) (z 1)) 0 ≤ flatten f z ∧
        flatten f z ≤ a.par.ℓ / a.par.β *
          (1 - Real.exp (-a.par.β * (a.par.T1 - z 0))) + 2 ∧
        -(a.par.ξ / a.par.r) * (1 - Real.exp (-a.par.r * (a.par.T1 - z 0))) ≤
          dy f (z 0) (z 1) (z 2) ∧
        dy f (z 0) (z 1) (z 2) ≤ 0 ∧ 0 ≤ dp f (z 0) (z 1) (z 2)) := by sorry

end RetirePartialInfo.Duality.Supplement
