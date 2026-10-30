-- Prove2me | Theorems.Thm_RobustDP_ChiSquareAudit_stationary_scan
-- name    : RobustDP.ChiSquareAudit.stationary_scan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:45:01.708212+00:00
-- url     : https://prove2.me/theorems/42bae7a4-f245-42cf-8b9d-c550fe1809b9
-- title:
--   Equation (54) and finite scan (corrected: coefficient and endpoint regimes)
-- statement:
--   Let $q$ be a strictly positive probability vector on $n$ coordinates, let $v$ be nondecreasing, and let $t\ge0$. Form the computed prefix cells. Write $F(\alpha)=E^q[\min(v,\alpha)]-\sqrt{t\operatorname{Var}^q[\min(v,\alpha)]}$ and $Q_j(\alpha)=c_j+b_j\alpha^2-(a_j+b_j\alpha)^2$.
--
--   If $\alpha$ is a local maximum of $F$, lies strictly between a cell's adjacent endpoints, and $Q_j(\alpha)>0$, then
--   $$b_j^2Q_j(\alpha)=t b_j^2((1-b_j)\alpha-a_j)^2.$$
--   Without any restriction on the optimizer's regime, executing the finite scan returns a threshold $\alpha_*$ between the smallest and largest input values and its exact score, satisfying
--   $$F(\alpha_*)=\max_{\alpha\in\mathbb R}F(\alpha).$$
--   The maximum is attained by the returned threshold, and the scan uses at most $192(n+1)$ charged operations after the prefix cells have been computed. This includes singleton support, equal values, zero radius, zero variance, saturation, linear or constant polynomials and zero discriminants. It does not assert stationarity for a boundary optimum.
--
--   This is the source's complete scalar solution step with its necessary corrections and endpoint completion. **Formalization Note** The numerical bound counts the defined exact-real execution; the source states only a linear scan bound.
--
--   Differences from the source:
--   - correction: equation (54) has right-hand side t(b(1-b)alpha-a)^2 → the right-hand side is t b^2((1-b)alpha-a)^2; reason: the same three-state instance in the variance correction is globally optimal at alpha=4: feasible p=(3/5,2/5,0) has divergence 14/25 and value 7/5 equal to the dual score; printed (54) gives 14/81=14/2025, whereas the corrected equation gives 14/81=14/81
--   - correction: every optimum satisfies f'(alpha)=0 and the scan need only check roots → stationarity is necessary at positive-variance interior optima; the unconditional scan also evaluates endpoints and covers zero polynomials, ties and degenerate cases; reason: q=(1/2,1/2), v=(0,1), t=4 has an optimum at alpha=0 with left and right slopes 1 and -1/2; this nonsmooth endpoint is not stationary
--   - generalization: the necessary stationary equation is asserted for a globally optimal threshold → the corrected interior equation holds at every local maximum; reason: every global maximum is a local maximum, so the source's complete corrected interior claim is included; the unconditional global scan conclusion is retained
--   - encoding: a sequential O(|S|) root scan after sorting → a fixed guarded quadratic/linear/endpoints scan with at most 192(n+1) charged operations on zero-based sorted coordinates; reason: this supplies the missing operational boundary rules; at most two explicit real roots per nonconstant polynomial and three scored candidates per cell preserve the stated exact arithmetic complexity
-- source:
--   G. Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07, revised May 4, 2004, p. 19, Section 4.2, proof of Lemma 5, (54) and ensuing complexity paragraph

import Mathlib
import Definitions.Def_RobustDP_ChiSquareAudit_Program

namespace RobustDP.ChiSquareAudit

open RobustDP.ChiSquare

/-- Corrected (54): b multiplies a on the right; stationarity applies to
differentiable interior extrema only. The finite scan covers every regime. -/
theorem stationary_scan (n : ℕ) (q v : Fin n → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hpos : ∀ i, 0 < q i)
    (hsorted : Monotone v) (t : ℝ) (ht : 0 ≤ t) :
      let rows := List.ofFn (fun i : Fin n => (⟨v i, q i, i.val⟩ : Row))
      let prefixes := prefixPass rows 0 1 0
      let execution := scanPass t prefixes.value none
      (∀ j : Fin n, ∀ high : ℝ,
        let cell := prefixes.value[j.val]?.getD default
        cell.high = some high → ∀ α : ℝ, cell.low < α → α < high →
        0 < intervalVariance cell.a cell.b cell.c α →
        IsLocalMax (scalarObjective q t v) α →
        cell.b ^ 2 * intervalVariance cell.a cell.b cell.c α =
          t * cell.b ^ 2 * ((1 - cell.b) * α - cell.a) ^ 2) ∧
      ∃ best : Best, execution.value = some best ∧
        best.val = scalarObjective q t v best.alpha ∧
        IsGreatest ((scalarObjective q t v) '' Set.univ) best.val ∧
        (∃ i j : Fin n, v i ≤ best.alpha ∧ best.alpha ≤ v j) ∧
        execution.steps ≤ 192 * (n + 1) := by sorry

end RobustDP.ChiSquareAudit
