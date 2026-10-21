-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_product
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:17:04.85476+00:00
-- url     : https://prove2.me/theorems/29b2b6d8-702b-4ddd-8e2a-171e710745bb
-- title:
--   Theorem 6.7
-- statement:
--   Let $X,Y$ be compact metric spaces, and let $\Phi,\Psi$ be Borel calculi on them acting on the same Hilbert space $H$. Assume $\Phi(f)\Psi(g)=\Psi(g)\Phi(f)$ only for $f\in C(X;k)$ and $g\in C(Y;k)$. There is a unique Borel calculus $P$ on $X\times Y$ such that, for all bounded Borel symbols $f,g$,
--
--   $$P(f\otimes g)=\Phi(f)\Psi(g),\qquad (f\otimes g)(x,y)=f(x)g(y).$$
--
--   Uniqueness concerns the entire calculus, including unbounded symbols.
--
--   This constructs the joint product calculus from commuting continuous restrictions.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 28, Theorem 6.7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Theorem 6.7, PDF pp.28–29: continuous commutation suffices for the unique full Borel product calculus. -/
theorem calculus_product [MetricSpace X] [MetricSpace Y] [BorelSpace X] [BorelSpace Y]
    [CompactSpace X] [CompactSpace Y]
    (F : Symbol X k → Relation H) (G : Symbol Y k → Relation H) (hF : Calculus F) (hG : Calculus G)
    (hcomm : ∀ f : C(X, k), ∀ g : C(Y, k),
      mul (F (continuousSymbol f)) (G (continuousSymbol g)) = mul (G (continuousSymbol g)) (F (continuousSymbol f))) :
    ∃! P : Symbol (X × Y) k → Relation H, Calculus P ∧
      ∀ f g, BoundedSymbol f → BoundedSymbol g →
        P ⟨fun p => f.val p.1 * g.val p.2, (f.property.comp measurable_fst).mul (g.property.comp measurable_snd)⟩ =
          mul (F f) (G g) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
