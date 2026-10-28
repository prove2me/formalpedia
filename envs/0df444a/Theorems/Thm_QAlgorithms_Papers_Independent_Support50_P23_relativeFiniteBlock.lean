-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_relativeFiniteBlock
-- name    : QAlgorithms.Papers.Independent.Support50.P23.relativeFiniteBlock
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:09:50.962858+00:00
-- url     : https://prove2.me/theorems/e6d29040-1555-4b01-b8c2-e28bae20a004
-- title:
--   Relative-entropy finite-block reformulation
-- statement:
--   Let $\rho,\sigma$ be normalized states on a finite-dimensional nonzero complex Hilbert space and let $n\ge1$. Use binary Umegaki relative entropy $S$ and Petz relative entropies $S_\alpha$, and set $\eta=2^{S_{3/2}(\rho\|\sigma)/2}+2^{-S_{1/2}(\rho\|\sigma)/2}+1$. On the finite-$\eta$ branch, for $0<\varepsilon<1$ and $n\ge\frac85\log_2(2/\varepsilon^2)$,
--   $$
--   \frac1n D_{\max}^{\varepsilon}(\rho^{\otimes n}\|\sigma^{\otimes n})
--   \le S(\rho\|\sigma)+\frac{4\log_2\eta\sqrt{\log_2(2/\varepsilon^2)}}{\sqrt n}.
--   $$
--   Here $D_{\max}^{\varepsilon}$ is the negative fixed-reference smooth min entropy with trivial first system, so smoothing is an infimum over this paper's subnormalized sine-distance ball. Support failure gives $S=+\infty$ and a trivial upper bound. For $\varepsilon\ge1$, the smooth max relative entropy is $-\infty$. This is the stated reformulation of Remark 10.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 6, Section V footnote 9, unnumbered: relative-entropy version

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Section V footnote 9, PDF p.6: relative-entropy version with THIS paper's
smoothing. Positive n and finite-eta real-domain guards agree with Remark 10;
support failure gives the trivial +infinity upper bound. -/
theorem relativeFiniteBlock [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ relativeUpsilon rho sigma ≠ ⊤ ∧
        (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon ≤
          relativeEntropy rho sigma +
            ((aepBlockError epsilon (relativeUpsilon rho sigma) / Real.sqrt (n : ℝ) : ℝ) : EReal)) ∧
    (¬ supportedBy rho sigma → relativeEntropy rho sigma = ⊤ ∧
      (((n : ℝ)⁻¹ : ℝ) : EReal) *
        smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon ≤
          relativeEntropy rho sigma) ∧
    (1 ≤ epsilon →
      smoothMaxRelative (matrixPower rho n) (matrixPower sigma n) epsilon = ⊥) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
