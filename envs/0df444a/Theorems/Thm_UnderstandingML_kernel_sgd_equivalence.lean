-- Prove2me | Theorems.Thm_UnderstandingML_kernel_sgd_equivalence
-- name    : UnderstandingML.kernel_sgd_equivalence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:49:11.82987+00:00
-- url     : https://prove2.me/theorems/bedfb009-61d3-4e9c-a58d-f05947c610da
-- title:
--   Lemma 16.3: SGD for Soft-SVM with kernels reproduces the feature-space SGD of §15.5: θ⁽ᵗ⁾ = ∑ⱼ βⱼ⁽ᵗ⁾ψ(xⱼ) for all t, and w̄ = ∑ⱼ ᾱⱼψ(xⱼ)
-- statement:
--   **Lemma 16.3.** Let $\hat w$ be the output of the SGD procedure described in Section 15.5 when applied on the feature space, and let $\bar w = \sum_{j=1}^m \bar\alpha_j\psi(x_j)$ be the output of applying SGD with kernels. Then $\bar w = \hat w$.
--
--   Formally: for the two procedures driven by the same sequence of chosen indices, $\theta^{(t)} = \sum_j \beta^{(t)}_j\psi(x_j)$ for every $t$ (16.6), hence the outputs coincide for every $T$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.3 pp. 223-224, Lemma 16.3 with its proof

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

namespace UnderstandingML

/-- **Lemma 16.3** (p. 223). Let `ŵ` be the output of the SGD procedure of §15.5 applied in the
feature space, and let `w̄ = ∑ⱼ ᾱⱼ ψ(xⱼ)` be the output of SGD with kernels (both driven by the
same sequence of chosen indices). Then `w̄ = ŵ`; indeed `θ⁽ᵗ⁾ = ∑ⱼ βⱼ⁽ᵗ⁾ ψ(xⱼ)` for every `t`
(16.6). -/
theorem kernel_sgd_equivalence {X : Type u} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {m : ℕ} (ψ : X → F) (K : X → X → ℝ)
    (hK : ∀ a b, K a b = ⟪ψ a, ψ b⟫_ℝ) (x : Fin m → X) (y : Fin m → ℝ) (lam : ℝ)
    (idx : ℕ → Fin m) :
    (∀ t, svmSgdTheta ψ x y lam idx t = ∑ j, kernelSgdBeta K x y lam idx t j • ψ (x j)) ∧
    ∀ T, svmSgdAverage ψ x y lam idx T =
      ∑ j, kernelSgdAlphaBar K x y lam idx T j • ψ (x j) := by sorry

end UnderstandingML
