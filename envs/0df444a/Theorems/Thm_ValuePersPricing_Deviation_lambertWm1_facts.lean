-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lambertWm1_facts
-- name    : ValuePersPricing.Deviation.lambertWm1_facts
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:21.672105+00:00
-- url     : https://prove2.me/theorems/acbbbc12-3631-419d-b19b-7c3ecf89415d
-- title:
--   App. A, p. ec1 — W₋₁(x) is the solution of we^w = x in (−∞, −1]; W₋₁(−1/e) = −1, W₋₁(x) → −∞ as x → 0⁻, W₋₁ non-increasing (corrected: one solution at −1/e)
-- statement:
--   Let $W_{-1}$ denote the negative real branch of the Lambert $W$ function. Then:
--
--   1. for every $x\in(-1/e,0)$ the equation $we^w=x$ has exactly two real solutions, and for $x=-1/e$ its only real solution is $w=-1$;
--   2. for every $x\in[-1/e,0)$, $W_{-1}(x)\le -1$, $W_{-1}(x)e^{W_{-1}(x)}=x$, and $W_{-1}(x)$ is the only solution of $we^w=x$ in $(-\infty,-1]$;
--   3. $W_{-1}(-1/e)=-1$;
--   4. $$\lim_{x\to 0^-}W_{-1}(x)=-\infty;$$
--   5. $W_{-1}$ is non-increasing on $[-1/e,0)$.
--
--   These are the properties of $W_{-1}$ used throughout the proofs of Theorem 2 and Lemmas 2, EC.1 and EC.2: the defining equation turns the integral inequalities into closed-form bounds, and monotonicity lets one apply $W_{-1}$ to both sides of an inequality.
--
--   **Formalization Note** `lambertWm1` is defined by choice with the junk value $0$ off $[-1/e,0)$; the statement never evaluates it there. The limit is one-sided, from the left, because $W_{-1}$ is defined only on $[-1/e,0)$.
--
--   Differences from the source:
--   - correction: "When x ∈ [−1/e, 0), this equation has two distinct real solutions" → two solutions for x ∈ (−1/e, 0) and the single solution −1 at x = −1/e; reason: at x = −1/e, w e^w attains its minimum −1/e only at w = −1, so the printed claim is false there.
--   - encoding: lim_{x→0} W₋₁(x) = −∞ → limit along x → 0 from the left; reason: W₋₁ is defined only on [−1/e, 0).
--   - generalization: App. A, p. ec1 states the equation, the range, the value at −1/e and the limit → Lean also states that W₋₁ is non-increasing on [−1/e, 0); reason: the paper asserts this on pp. ec2, ec4 and ec6 and uses it in every Lambert-W step; the extra conjunct only adds to the App. A statement.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), App. A, p. ec1 (PDF 33); monotonicity: pp. ec2, ec4, ec6 (PDF 34, 36, 38)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- App. A (p. ec1): `w e^w = x` has exactly two real solutions for `x ∈ (−1/e, 0)` and the single
solution `−1` at `x = −1/e` (corrected: the printed "two distinct real solutions" for
`x ∈ [−1/e, 0)` fails at `−1/e`); on `[−1/e, 0)`, `W₋₁(x)` is the unique solution in `(−∞, −1]`;
`W₋₁(−1/e) = −1`; `W₋₁(x) → −∞` as `x → 0⁻`; and `W₋₁` is non-increasing on `[−1/e, 0)`
(asserted on pp. ec2, ec4, ec6). -/
theorem lambertWm1_facts :
    (∀ x ∈ Ioo (-1 / Real.exp 1) 0, {w : ℝ | w * Real.exp w = x}.ncard = 2) ∧
    {w : ℝ | w * Real.exp w = -1 / Real.exp 1} = {-1} ∧
    (∀ x : ℝ, -1 / Real.exp 1 ≤ x → x < 0 →
      lambertWm1 x ≤ -1 ∧ lambertWm1 x * Real.exp (lambertWm1 x) = x ∧
      ∀ w : ℝ, w ≤ -1 → w * Real.exp w = x → w = lambertWm1 x) ∧
    lambertWm1 (-1 / Real.exp 1) = -1 ∧
    Tendsto lambertWm1 (𝓝[<] 0) atBot ∧
    AntitoneOn lambertWm1 (Ico (-1 / Real.exp 1) 0) := by sorry

end ValuePersPricing.Deviation
