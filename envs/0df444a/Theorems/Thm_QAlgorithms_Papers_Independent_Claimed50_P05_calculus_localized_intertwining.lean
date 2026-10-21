-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_localized_intertwining
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_localized_intertwining
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:12:43.696988+00:00
-- url     : https://prove2.me/theorems/3198dd6b-686f-4682-9710-4c9a85d69251
-- title:
--   Lemma 5.4
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   Let $K,\Psi,T$ be as in the intertwining theorem, and write $E(\Phi,\Psi;T)$ for its intertwining set. For $A\in\Sigma$ define $T_A=\Psi(1_A)T\Phi(1_A)$. For every $f\in M(X)$, both implications hold:
--
--   $$f\in E(\Phi,\Psi;T)\ \Longrightarrow\ f1_A\in E(\Phi,\Psi;T_A)\ \Longrightarrow\ f\in E(\Phi,\Psi;T_A).$$
--
--   The localized operator is constructed from the two actual indicator operators.
--
--   This is localization of the intertwining relation.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 20, Lemma 5.4

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

/-- Lemma 5.4, PDF pp.20–21: both implications for the concretely localized intertwiner. -/
theorem calculus_localized_intertwining (F : Symbol X k → Relation H) (G : Symbol X k → Relation K)
    (hF : Calculus F) (hG : Calculus G) (T : H →L[k] K) (f : Symbol X k)
    (A : Set X) (hA : MeasurableSet A) :
    ∃ (P : H →L[k] H) (Q : K →L[k] K),
      F (indicator A hA) = boundedGraph P ∧ G (indicator A hA) = boundedGraph Q ∧
      (Intertwines F G T f → Intertwines F G (Q.comp (T.comp P)) (times f (indicator A hA))) ∧
      (Intertwines F G (Q.comp (T.comp P)) (times f (indicator A hA)) →
        Intertwines F G (Q.comp (T.comp P)) f) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
