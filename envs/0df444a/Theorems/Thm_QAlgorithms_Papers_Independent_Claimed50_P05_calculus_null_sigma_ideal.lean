-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_null_sigma_ideal
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_null_sigma_ideal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:22:02.122541+00:00
-- url     : https://prove2.me/theorems/e3291bc4-c40b-46d1-b3bc-f2801e4416fe
-- title:
--   §3.1, unnumbered: null sets form a sigma ideal
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   The collection $\mathcal N_\Phi=\{A\in\Sigma:\Phi(1_A)=0\}$ is a sigma ideal relative to $\Sigma$:
--
--   $$\varnothing\in\mathcal N_\Phi,\quad A\in\Sigma,\ A\subseteq B\in\mathcal N_\Phi\Rightarrow A\in\mathcal N_\Phi,\quad A_n\in\mathcal N_\Phi\Rightarrow\bigcup_n A_n\in\mathcal N_\Phi.$$
--
--   Downward closure concerns measurable subsets only.
--
--   This defines the almost-everywhere calculus equivalence relation.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 14, §3.1, unnumbered: null sets form a sigma ideal

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

/-- Section 3.1, PDF p.14: sigma ideal relative to the given measurable sigma algebra. -/
theorem calculus_null_sigma_ideal (F : Symbol X k → Relation H) (hF : Calculus F) :
    Null F ∅ ∧
    (∀ A B : Set X, MeasurableSet A → A ⊆ B → Null F B → Null F A) ∧
    (∀ A : ℕ → Set X, (∀ n, Null F (A n)) → Null F (⋃ n, A n)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
