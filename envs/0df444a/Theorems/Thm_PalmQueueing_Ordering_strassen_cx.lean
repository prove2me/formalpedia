-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_strassen_cx
-- name    : PalmQueueing.Ordering.strassen_cx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T03:37:19.137583+00:00
-- url     : https://prove2.me/theorems/e258026b-019c-45e9-8ba9-80dbd76b9a63
-- title:
--   Theorem 4.2.2 — Strassen's ≤_cx theorem
-- statement:
--   **Theorem 4.2.2 (Strassen's $\le_{cx}$ theorem).** Let $F$ and $G$ be two **integrable**
--   distributions in $\mathcal{D}(\mathbb{R}^n)$; $F \le_{cx} G$ (resp. $F \le_{icx} G$) **if and only
--   if** there exist two $\mathbb{R}^n$-valued random variables $X$ and $Y$ defined on the same
--   probability space with distributions $F$ and $G$ respectively, and such that $E[Y \mid X] = X$
--   (resp. $E[Y \mid X] \ge X$) a.s.
--
--   The convex order holds exactly when the larger distribution is a **martingale dilation** of the
--   smaller: $G$ is obtained from $F$ by spreading each point out without moving its conditional mean.
--   This is the classical Strassen representation, and it is what makes the convex order tractable —
--   comparison results for queues become induction arguments on a coupling rather than analytic
--   manipulations of convolutions of c.d.f.'s.
--
--   Both clauses are stated, as the book states them together: $\le_{cx}$ with $E[Y \mid X] = X$ and
--   $\le_{icx}$ with $E[Y \mid X] \ge X$.
--
--   **Both directions are asserted.** The hard one is the construction of the coupling; a
--   one-directional statement would be the easy half, since Jensen's inequality gives $F \le_{cx} G$
--   from any such pair immediately.
--
--   $E[Y \mid X]$ is a **conditional expectation**, not an equality of expectations: the content is
--   that the identity holds a.s. given $X$.
--
--   **Integrability is a hypothesis here and not in Theorem 4.2.1.** The convex order needs first
--   moments; the stochastic order does not. The two are not harmonised.
--
--   The book attributes both theorems to Strassen (1965) and proves neither. Example 4.2.3 on the same
--   page shows the construction at work: for the comparison of exponential and Erlang distributions,
--   symmetry makes $E[Y_i \mid X]$ a function $\Psi(X)$ independent of $i$, and
--   $\Psi(X) = E[\frac{1}{n}\sum_i Y_i \mid X] = E[X/n \mid X] = X/n$ a.s.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 278, Theorem 4.2.2

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

/-!
# Theorem 4.2.2: Strassen's `≤_cx` theorem (§4.2.3, p.278)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Theorem 4.2.2 (Strassen's `≤_cx` theorem)** (p.278). Let `F` and `G` be two integrable
distributions in `𝒟(ℝⁿ)`; `F ≤_cx G` (resp. `F ≤_icx G`) **if and only if** there exist two
`ℝⁿ`-valued random variables `X` and `Y` defined on the same probability space with distributions
`F` and `G` respectively, and such that `E[Y | X] = X` (resp. `E[Y | X] ≥ X`) a.s.

The convex order holds exactly when the larger distribution is a **martingale dilation** of the
smaller: `G` is obtained from `F` by spreading each point out without moving its conditional mean.
That is the classical Strassen representation, and it is what makes the convex order tractable —
comparison results for queues become induction arguments on a coupling, rather than analytic
manipulations of convolutions of c.d.f.'s.

Both clauses are in the statement, as the book states them together: the `≤_cx` case with
`E[Y | X] = X` and the `≤_icx` case with `E[Y | X] ≥ X`.

**Both directions are asserted.** The hard one is the construction of the coupling; a
one-directional statement would be the easy half, since Jensen's inequality gives `F ≤_cx G` from
any such pair immediately.

`E[Y | X]` is a **conditional expectation**, not an equality of expectations: the whole content is
that the identity holds pointwise a.s. given `X`.

**Integrability is a hypothesis here and not in Theorem 4.2.1.** The convex order needs first
moments; the stochastic order does not. The two theorems are not harmonised.

The book attributes both to Strassen and does not prove them: "The next two theorems on the
pathwise representation of stochastic orders are proved in Strassen (1965)." -/
theorem strassen_cx {n : ℕ} (F G : Measure (Fin n → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G)
    (hFi : IsIntegrableDist F) (hGi : IsIntegrableDist G) :
    (CxLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        condExp (MeasurableSpace.comap X inferInstance) P Y =ᵐ[P] X) ∧
    (IcxLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω)
          (condExp (MeasurableSpace.comap X inferInstance) P Y ω)) := by sorry

end PalmQueueing.Ordering
