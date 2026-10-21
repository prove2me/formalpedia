-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_spectral_support
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_spectral_support
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:07:45.574444+00:00
-- url     : https://prove2.me/theorems/c3332c9a-350a-436d-97a9-4737acccf42a
-- title:
--   Corollary 4.2
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For $f\in M(X)$, let $\Phi^f(g)=\Phi(g\circ f)$ be its push-forward calculus on $k$. Then
--
--   $$\sigma_p(\Phi(f))\subseteq f(X),\qquad\sigma(\Phi(f))=\operatorname{supp}(\Phi^f)\subseteq\overline{f(X)}.$$
--
--   The push-forward $\Phi^f$ is concentrated on $\sigma(\Phi(f))$. The first inclusion has no closure.
--
--   This identifies the spectrum as a support of a transported calculus.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 17, Corollary 4.2

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

/-- Corollary 4.2, PDF p.17: the spectrum uses closure of the image, and the final concentration. -/
theorem calculus_spectral_support (F : Symbol X k → Relation H) (hF : Calculus F)
    (f : Symbol X k) :
    pointSpectrum (k := k) (F f) ⊆ Set.range f.val ∧
    spectrumOf (k := k) (F f) = calculusSupport (push F f.val f.property) ∧
    spectrumOf (k := k) (F f) ⊆ closure (Set.range f.val) ∧
    Concentrated (push F f.val f.property) (spectrumOf (k := k) (F f)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
