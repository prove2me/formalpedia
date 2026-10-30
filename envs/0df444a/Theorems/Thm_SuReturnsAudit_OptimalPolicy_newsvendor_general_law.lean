-- Prove2me | Theorems.Thm_SuReturnsAudit_OptimalPolicy_newsvendor_general_law
-- name    : SuReturnsAudit.OptimalPolicy.newsvendor_general_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:43:58.848998+00:00
-- url     : https://prove2.me/theorems/dd8b89f7-fd70-4a00-9063-8267717d4809
-- title:
--   Appendix A, final newsvendor calculation (corrected: demand-atom quantile condition)
-- statement:
--   Let $D$ be the law of a nonnegative real demand $X$. No finite-mean or continuity assumption is made. For a finite stock $q\ge0$, write $T(q)=\mathbb E_D\min(X,q)$. Let $A,B\in\mathbb R$ satisfy $0<B<A$, and set $L(q)=AT(q)-Bq$.
--
--   There exists a finite $q^*\ge0$ satisfying the critical-quantile bracket. Moreover, for every $q\ge0$,
--
--   $$
--   \bigl[\forall t\ge0,\ L(t)\le L(q)\bigr]
--   \quad\Longleftrightarrow\quad
--   \Pr_D(X>q)\le\frac BA\le\Pr_D(X\ge q).
--   $$
--
--   For every such bracket quantity $q$, if $D(\{q\})=0$, then $1-F(q)=B/A$, where $F(q)=\Pr_D(X\le q)$.
--
--   This is the complete general-demand quantity step in Proposition 2. It specializes to $A=R(s)-s$ and $B=c-s$ and permits zero demand, demand atoms, gaps, and infinite mean demand. For each finite nonnegative stock the sales integrand is bounded, so its expectation is an actual integral.
--
--   Differences from the source:
--   - correction: equation (10) and the final calculation require an exact demand-tail equality → strict/weak demand-tail quantile brackets, with the exact equality retained at atomless optimal quantities; reason: X=1 almost surely, V uniform on [1,3], s=0, c=1 satisfy all source assumptions, but the unique optimal q=1 has critical ratio 1/2 and the strict tail never equals 1/2
--   - generalization: the final inventory calculation uses A=R(s)-s and B=c-s and gives an optimal quantity → arbitrary real coefficients 0<B<A, finite quantity existence, and an iff characterization of every nonnegative maximizer; reason: the source coefficients satisfy 0<B<A under its standing assumptions, so the full source inventory claim is recovered
--   - encoding: nonnegative market size X and its demand distribution F → a probability measure D on the real numbers with D((-infinity,0))=0, and real-valued strict/weak tail probabilities; reason: this represents exactly the law of nonnegative demand; probability finiteness makes conversion to real numbers exact
-- source:
--   Su, Consumer Returns Policies and Supply Chain Performance, SSRN 1020451, August 2008 manuscript, https://ssrn.com/abstract=1020451, printed/PDF p. 26, proof of Proposition 2, final newsvendor calculation; equation (10), printed/PDF p. 11.

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace SuReturnsAudit.OptimalPolicy

/-- Su, August 2008 SSRN manuscript, proof of Proposition 2, p. 26, final
newsvendor calculation tied to (10), p. 11. Corrected for demand atoms:
the critical ratio lies between the strict and weak upper tails.
Arbitrary coefficients `0 < B < A` include the paper's coefficients.
Demand has no moment or continuity assumption; finite stock bounds sales. -/
theorem newsvendor_general_law (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD0 : D (Set.Iio 0) = 0) (A B : ℝ) (hB : 0 < B) (hBA : B < A) :
    (∃ qstar : ℝ, 0 ≤ qstar ∧
      (D (Set.Ioi qstar)).toReal ≤ B / A ∧ B / A ≤ (D (Set.Ici qstar)).toReal) ∧
    (∀ q : ℝ, 0 ≤ q →
      ((∀ t : ℝ, 0 ≤ t →
          A * SupplyChainTheory.expSales D t - B * t ≤
            A * SupplyChainTheory.expSales D q - B * q) ↔
        (D (Set.Ioi q)).toReal ≤ B / A ∧ B / A ≤ (D (Set.Ici q)).toReal) ∧
      ((D (Set.Ioi q)).toReal ≤ B / A → B / A ≤ (D (Set.Ici q)).toReal →
        D {q} = 0 → 1 - cdf D q = B / A)) := by sorry

end SuReturnsAudit.OptimalPolicy
