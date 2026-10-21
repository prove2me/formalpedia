-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_spectral_properties
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_spectral_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:07:26.708366+00:00
-- url     : https://prove2.me/theorems/499e8112-68f1-421d-9ce6-aacbef3c2d4c
-- title:
--   Theorem 4.1
-- statement:
--   Let $k$ be $\mathbb R$ or $\mathbb C$, let $H$ be a Hilbert space, and let $(X,\Sigma)$ be a measurable space. Write $M(X)$ for the finite $k$-valued measurable functions with pointwise equality, and $M_b(X)$ for its bounded functions. Let $\Phi:M(X)\to C(H)$ satisfy axioms MFC1–MFC5, where $C(H)$ consists of closed functional linear graphs. All operator equalities include equality of domains; an overline on an operator denotes graph closure.
--
--   For $f\in M(X)$ define
--
--   $$\operatorname{essran}_\Phi f=\{\lambda\in k:\ \forall\varepsilon>0,\ \{x:|f(x)-\lambda|\le\varepsilon\}\text{ is not }\Phi\text{-null}\}.$$
--
--   For $c\ge0$ and $\lambda\in k$, all of the following hold: $\sigma(\Phi(f))=\sigma_{\rm ap}(\Phi(f))=\operatorname{essran}_\Phi f$; $f$ belongs to this essential range $\Phi$-almost everywhere; boundedness together with $\|\Phi(f)\|\le c$ is equivalent to $|f|\le c$ $\Phi$-almost everywhere; self-adjointness of $\Phi(f)$ is equivalent to reality of $f$ $\Phi$-almost everywhere; and $\lambda$ is an eigenvalue exactly when $\{f=\lambda\}$ is not $\Phi$-null. Finally, $\Phi(1_{\{f=\lambda\}})$ is the orthogonal projection onto $\ker(\lambda I-\Phi(f))$. Here $\sigma$ is the spectrum defined by everywhere-defined bounded inverse resolvents, and $\sigma_{\rm ap}$ uses unit approximate eigenvectors in the operator domain.
--
--   This determines spectral information directly from the symbol.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 15, Theorem 4.1

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

/-- Theorem 4.1, PDF pp.15–17: all spectral, order, reality, and eigenspace conclusions. -/
theorem calculus_spectral_properties (F : Symbol X k → Relation H) (hF : Calculus F)
    (f : Symbol X k) (c : ℝ) (hc : 0 ≤ c) (z : k) :
    (spectrumOf (k := k) (F f) = approximateSpectrum (k := k) (F f) ∧
      approximateSpectrum (k := k) (F f) = essentialRange F f) ∧
    Almost F (fun x => f.val x ∈ essentialRange F f) ∧
    (NormBound (k := k) (F f) c ↔ Almost F (fun x => ‖f.val x‖ ≤ c)) ∧
    (SelfAdjoint (k := k) (F f) ↔ Almost F (fun x => star (f.val x) = f.val x)) ∧
    ((z ∈ pointSpectrum (k := k) (F f) ↔ ¬ Null F {x | f.val x = z}) ∧
      ∀ hz : MeasurableSet {x | f.val x = z},
        ProjectionOnto (k := k) (F (indicator {x | f.val x = z} hz))
          (kernel (resolventShift z (F f)))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
