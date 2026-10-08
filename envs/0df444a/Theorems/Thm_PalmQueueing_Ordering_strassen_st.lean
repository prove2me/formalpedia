-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_strassen_st
-- name    : PalmQueueing.Ordering.strassen_st
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T03:12:34.139715+00:00
-- url     : https://prove2.me/theorems/e13fd3ad-7083-4021-a5b2-2185367ad484
-- title:
--   Theorem 4.2.1 — Strassen's ≤_i theorem
-- statement:
--   **Theorem 4.2.1 (Strassen's $\le_i$ theorem).** For $F$ and $G$ in
--   $\mathcal{D}(\mathbb{R}^n)$, $F \le_i G$ **if and only if** there exist two $\mathbb{R}^n$-valued
--   random variables $X$ and $Y$ defined on the same probability space with probability distribution
--   $F$ and $G$ respectively, and such that $X \le Y$ a.s.
--
--   The stochastic order holds exactly when the two distributions can be **coupled monotonically**.
--   The book explains what the pointwise representations are for: they "provide a natural way for
--   handling integral ordering in higher dimensions, at least whenever the independence assumptions of
--   Property 4.2.3 are not satisfied ... particularly useful to establish comparison properties of
--   embedded sequences in various queueing systems by simple induction arguments, which replace the
--   usual analytical proofs, based on stability properties of the integral order with respect to
--   convolutions or products of c.d.f."
--
--   In dimension $1$ the coupling is explicit: take $U$ uniform on $[0,1]$ and set $X = F^{-1}(U)$,
--   $Y = G^{-1}(U)$ with $F^{-1}(u) = \inf\{x;\ F(x) > u\}$. In dimension $n$ there is no such formula,
--   which is why the theorem is Strassen's.
--
--   Both directions are asserted; the converse is immediate and the construction of the coupling is the
--   theorem. **No integrability hypothesis**, unlike Theorem 4.2.2.
--
--   The book attributes it to Strassen and does not prove it: "The next two theorems on the pathwise
--   representation of stochastic orders are proved in Strassen (1965).\"
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 277, Theorem 4.2.1

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

/-!
# Theorem 4.2.1: Strassen's `≤_i` theorem (§4.2.3, p.277)
-/

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Theorem 4.2.1 (Strassen's `≤_i` theorem)** (p.277). For `F` and `G` in `𝒟(ℝⁿ)`, `F ≤_i G`
**if and only if** there exist two `ℝⁿ`-valued random variables `X` and `Y` defined on the same
probability space with probability distribution `F` and `G` respectively, and such that `X ≤ Y`
a.s.

The stochastic order holds exactly when the two distributions can be **coupled monotonically**.
This is the pathwise representation that makes the order usable in higher dimensions: "These
representations are particularly useful to establish comparison properties of embedded sequences
in various queueing systems by simple induction arguments, which replace the usual analytical
proofs, based on stability properties of the integral order with respect to convolutions or
products of c.d.f."

Both directions are asserted; the converse — that a monotone coupling gives the order — is
immediate, and the construction of the coupling is the theorem.

In dimension `1` the coupling is explicit and the book gives it: take `U` uniform on `[0,1]` and
set `X = F^{-1}(U)`, `Y = G^{-1}(U)` with `F^{-1}(u) = inf{x; F(x) > u}`. In dimension `n` no such
formula is available, which is why the theorem is Strassen's.

**No integrability hypothesis**, unlike Theorem 4.2.2: the stochastic order does not need first
moments. -/
theorem strassen_st {n : ℕ} (F G : Measure (Fin n → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G) :
    StLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω) (Y ω) := by sorry

end PalmQueueing.Ordering
