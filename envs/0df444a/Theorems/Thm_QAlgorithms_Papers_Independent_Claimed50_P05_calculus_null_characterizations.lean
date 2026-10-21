-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_null_characterizations
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_null_characterizations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:06:13.906844+00:00
-- url     : https://prove2.me/theorems/36fc0289-550d-42b2-8341-dd93b5cee45c
-- title:
--   Lemma 3.1
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   A measurable set $A$ is $\Phi$-null when $\Phi(1_A)$ is the everywhere-defined zero operator. A property holds $\Phi$-almost everywhere when its failure set is $\Phi$-null. For $f,g\in M(X)$,
--
--   $$\begin{aligned}
--   \ker\Phi(f)&=\ker\Phi(1_{\{f\ne0\}}),\\
--   \Phi(f)=0&\Longleftrightarrow f=0\quad\Phi\text{-a.e.},\\
--   \Phi(f)=\Phi(g)&\Longleftrightarrow f=g\quad\Phi\text{-a.e.},\\
--   \Phi(f)\text{ injective}&\Longleftrightarrow f\ne0\quad\Phi\text{-a.e.}
--   \end{aligned}$$
--
--   This relates graph equality and kernels to the calculus null ideal.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 14, Lemma 3.1

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

/-- Lemma 3.1, PDF p.14: kernels, null symbols, coincidence, and injectivity. -/
theorem calculus_null_characterizations (F : Symbol X k → Relation H) (hF : Calculus F) :
    (∀ (f : Symbol X k) (h : MeasurableSet {x | f.val x ≠ 0}),
      kernel (F f) = kernel (F (indicator {x | f.val x ≠ 0} h))) ∧
    (∀ f, F f = zeroGraph ↔ Almost F (fun x => f.val x = 0)) ∧
    (∀ f g, F f = F g ↔ Almost F (fun x => f.val x = g.val x)) ∧
    (∀ f, InjectiveOperator (F f) ↔ Almost F (fun x => f.val x ≠ 0)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
