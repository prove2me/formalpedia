-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_continuous_regular_spectral_correspondence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.continuous_regular_spectral_correspondence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:33:32.828941+00:00
-- url     : https://prove2.me/theorems/2efd35bf-a7c3-475f-a689-bdd29597b431
-- title:
--   Theorem 1.3
-- statement:
--   Let $M$ be Hausdorff. Every continuous $f:M\to\mathbb R$ induces the regular spectral family
--
--   $$\sigma_f(\lambda)=\operatorname{int}\bigl(f^{-1}(({-\infty},\lambda])\bigr).$$
--
--   Its admissible domain is all of $M$, and its induced function is $f$. Conversely, for every regular spectral family $\sigma$, the domain $D(\sigma)$ is open and dense, all pointwise cuts there are finite, and $f_\sigma:D(\sigma)\to\mathbb R$ is continuous. The family induced by this function in the subspace topology is $\sigma(\lambda)\cap D(\sigma)$ for every real $\lambda$. This correspondence imposes neither compactness nor boundedness.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 14, Theorem 1.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Theorem 1.3; de Groote, Observables I, PDF p./pp. 14.
-/
theorem continuous_regular_spectral_correspondence {M : Type u} [TopologicalSpace M] [T2Space M] :
    (∀ f : M → ℝ, Continuous f → IsRegularSpectralFamily (openSublevels f) ∧
      admissibleDomain (openSublevels f) = Set.univ ∧
      spectralCutInfimum (fun t => (openSublevels f t : Set M)) = f) ∧
    (∀ E : ℝ → Opens M, IsRegularSpectralFamily E →
      IsOpen (admissibleDomain E) ∧ Dense (admissibleDomain E) ∧
      Continuous (fun x : admissibleDomain E => spectralCutInfimum (fun t => (E t : Set M)) x.val) ∧
      (∀ x ∈ admissibleDomain E, {t | x ∈ (E t : Set M)}.Nonempty ∧
        BddBelow {t | x ∈ (E t : Set M)}) ∧
      ∀ t : ℝ,
        (openSublevels (fun x : admissibleDomain E =>
          spectralCutInfimum (fun s => (E s : Set M)) x.val) t : Set (admissibleDomain E)) =
        {x | x.val ∈ (E t : Set M)}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
