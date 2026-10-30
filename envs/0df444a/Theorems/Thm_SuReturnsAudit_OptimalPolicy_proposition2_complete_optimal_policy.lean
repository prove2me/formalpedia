-- Prove2me | Theorems.Thm_SuReturnsAudit_OptimalPolicy_proposition2_complete_optimal_policy
-- name    : SuReturnsAudit.OptimalPolicy.proposition2_complete_optimal_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:44:18.619992+00:00
-- url     : https://prove2.me/theorems/4abd3da8-639e-47f7-b131-d2021373f971
-- title:
--   Proposition 2 — complete optimal policy (corrected: demand-atom quantile condition)
-- statement:
--   Let $D$ be the law of a nonnegative real market size $X$, and let $\nu$ be an integrable real valuation law with mean $\mu=\mathbb E_\nu V$. Assume $0\le s<c<\mu$, where $c$ is unit cost and $s$ is the common salvage value of unsold and returned units. Define $R(r)=\mathbb E_\nu\max(V,r)$, $K(r)=\Pr_\nu(V\ge r)$, and $H(r)=\Pr_\nu(V<r)$. For any real price $p$, refund $r$, and stock $q\ge0$, sales are $S=T(q)=\mathbb E_D\min(X,q)$ if $p\le R(r)$ and zero otherwise. The expected cash-flow profit is
--
--   $$
--   \Pi(p,q,r)=pK(r)S+(p-r+s)H(r)S+s(q-S)-cq.
--   $$
--
--   Set $p^*=R(s)$, $r^*=s$, and $\alpha=(c-s)/(p^*-s)$. Then $0\le r^*<p^*$ and $0<\alpha<1$. There exists a finite real $q^*\ge0$ with
--
--   $$
--   \Pr_D(X>q^*)\le\alpha\le\Pr_D(X\ge q^*).
--   $$
--
--   Every nonnegative quantity satisfying this bracket is jointly optimal with the displayed price and refund:
--
--   $$
--   \forall p,r\in\mathbb R\ \forall q\ge0,\qquad
--   \Pi(p,q,r)\le\Pi(p^*,q^*,r^*).
--   $$
--
--   At every such $q^*$ with $D(\{q^*\})=0$, the exact source equation is recovered:
--
--   $$
--   \overline F(q^*)=\frac{c-s}{p^*-s}=\frac{c-s}{R(s)-s},
--   \qquad \overline F(q)=\Pr_D(X>q)=1-F(q).
--   $$
--
--   This is the complete corrected Proposition 2, including quantity existence and no-purchase deviations. It asserts that the displayed choices are optimal, not that every optimal price or refund is unique. It needs no finite demand mean, demand density, or atomlessness assumption.
--
--   Differences from the source:
--   - correction: equation (10) and the final calculation require an exact demand-tail equality → strict/weak demand-tail quantile brackets, with the exact equality retained at atomless optimal quantities; reason: X=1 almost surely, V uniform on [1,3], s=0, c=1 satisfy all source assumptions, but the unique optimal q=1 has critical ratio 1/2 and the strict tail never equals 1/2
--   - generalization: the valuation model is presented using a nonnegative valuation density g → any probability valuation law on the real numbers with integrable identity, including atoms and negative values; reason: the density model is a special case and the conclusion uses only integrable reservation prices and the stated mean ordering
--   - generalization: refunds are economically between zero and the price → the global bound compares against all real prices p and refunds r, while the proposed optimum satisfies 0<=rstar<pstar; reason: the cash-flow definition extends to all such deviations, so the bound includes the entire economic policy domain
--   - encoding: nonnegative market size, finite mean valuation, buy at price indifference, and keep when V>=r → probability measures, D((-infinity,0))=0, Integrable identity for valuation, explicit participation in profit, and strict/weak half-lines at ties; reason: these encode the standing model and its stated decisions without adding any demand moment or regularity assumption
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451, August 2008 manuscript, https://ssrn.com/abstract=1020451, Proposition 2, equations (9)–(11), printed/PDF p. 11; standing model pp. 6–7; participation (6), p. 10; cash flows (7)–(8), p. 11; proof p. 26.

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory SuReturns.PartialRefunds

namespace SuReturnsAudit.OptimalPolicy

/-- Su, August 2008 SSRN manuscript, Proposition 2, p. 11, (9)--(11),
proof p. 26. Complete joint optimum, including finite inventory existence.
Correction: (10) must be a quantile bracket for demand laws with atoms;
the printed equality is retained at every atomless optimal quantity.
For example X=1 a.s., V uniform on [1,3], s=0, c=1 has optimum q=1
but its strict demand tail never equals the printed critical ratio 1/2.
Generalizations: integrable real valuation laws and all real price/refund
deviations. The displayed optimum itself has 0 ≤ refund < price. -/
theorem proposition2_complete_optimal_policy (ν D : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure D]
    (hν : Integrable (fun v => v) ν) (hD0 : D (Set.Iio 0) = 0)
    (c s : ℝ) (hs : 0 ≤ s) (hsc : s < c) (hcμ : c < meanValuation ν) :
    let pstar := reservationPrice ν s
    let rstar := s
    let α := (c - s) / (pstar - s)
    (0 ≤ rstar ∧ rstar < pstar) ∧ (0 < α ∧ α < 1) ∧
    (∃ qstar : ℝ, 0 ≤ qstar ∧
      (D (Set.Ioi qstar)).toReal ≤ α ∧ α ≤ (D (Set.Ici qstar)).toReal) ∧
    (∀ qstar : ℝ, 0 ≤ qstar →
      (D (Set.Ioi qstar)).toReal ≤ α → α ≤ (D (Set.Ici qstar)).toReal →
      (∀ p q r : ℝ, 0 ≤ q →
        profit ν D c s p q r ≤ profit ν D c s pstar qstar rstar) ∧
      (D {qstar} = 0 →
        1 - cdf D qstar = (c - s) / (pstar - s) ∧
        (c - s) / (pstar - s) = (c - s) / (reservationPrice ν s - s))) := by sorry

end SuReturnsAudit.OptimalPolicy
