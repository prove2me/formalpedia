-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_lemma6_randomized_gentleness
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.lemma6_randomized_gentleness
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:05:59.044149+00:00
-- url     : https://prove2.me/theorems/358b97e8-e36a-4d79-8725-5369aac66959
-- title:
--   Lemma 6: randomized conjugated projective measurement is gentle
-- statement:
--   Let $\Lambda$ and $A$ be finite nonempty sets, $p$ a probability distribution, $V(\lambda)$ unitary, and $\{P_a\}_{a\in A}$ a complete family of self-adjoint orthogonal projectors, allowing zero projectors. Choose $\lambda$, apply $V(\lambda)$, measure, undo the same unitary, and discard the label. This defines
--
--   $$\mathcal G(\rho)=\sum_{\lambda,a}p(\lambda)V(\lambda)^\dagger P_aV(\lambda)\rho V(\lambda)^\dagger P_aV(\lambda).$$
--
--   For every density input, with $p_a(\rho)=\sum_\lambda p(\lambda)\operatorname{Tr}(P_aV(\lambda)\rho V(\lambda)^\dagger)$,
--
--   $$F(\rho,\mathcal G(\rho))\ge\max_{a\in A}p_a(\rho).$$
--
--   The maximum is attained. This is the randomized construction in H19–H21 for mixed states as well as pure states, rather than a hypothesis on an arbitrary channel.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 33, Lemma 6: randomized conjugated projective measurement is gentle

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.33–34, Lemma 6: the actual randomized conjugated measurement is gentle.
The expected probability has an attained maximum on the finite nonempty outcome type. -/
theorem lemma6_randomized_gentleness [Nonempty L] [Nonempty A]
    (p : L → ℝ) (hp : QAlgorithms.Learning.IsDistribution p) (V : L → Matrix.unitaryGroup I ℂ)
    (P : A → Matrix I I ℂ) (hP : ProjectiveFamily P) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    (∃ a : A, ∀ b : A, gentleProbability p (fun l => (V l : Matrix I I ℂ)) P rho b ≤
      gentleProbability p (fun l => (V l : Matrix I I ℂ)) P rho a) ∧
    (∀ a : A, gentleProbability p (fun l => (V l : Matrix I I ℂ)) P rho a ≤
      rootFidelity rho (gentleChannel p (fun l => (V l : Matrix I I ℂ)) P rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
