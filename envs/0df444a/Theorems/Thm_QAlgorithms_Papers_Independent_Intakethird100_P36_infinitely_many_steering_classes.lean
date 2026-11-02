-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_infinitely_many_steering_classes
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.infinitely_many_steering_classes
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:23:41.257196+00:00
-- url     : https://prove2.me/theorems/763133a7-0fa1-43a2-a9f1-a678948990bc
-- title:
--   Infinitely many inequivalent minimal-dimensional steering classes
-- statement:
--   On a qubit, consider two binary inputs and outputs. For \(0<\theta<\pi/4\), define \(\Psi^\theta_{a|x}=\tfrac12|\psi^\theta(a,x)\rangle\langle\psi^\theta(a,x)|\), where the input-zero basis is \((|0\rangle,|1\rangle)\) and the input-one basis is \((\cos\theta|0\rangle+\sin\theta|1\rangle,-\sin\theta|0\rangle+\cos\theta|1\rangle)\). These are normalized, pure orthogonal, steerable assemblages. For distinct parameters in this interval,
--
--   $$
--   \theta\ne\eta\quad\Longrightarrow\quad
--   \Psi^\theta\not\longrightarrow\Psi^\eta\ \text{ and }
--   \Psi^\eta\not\longrightarrow\Psi^\theta
--   $$
--
--   under stochastic 1W-LOCC with any strictly positive success probability. The family contains infinitely many distinct assemblages, so there are infinitely many inequivalent classes already at \(d=r=s=2\). Restricting the witness angles selects distinct classes even when all input and output relabelings are allowed.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 7, Section VIII; (F5), p.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Section VIII, PDF p.7, with the witness family (F5), p.15. Restricting angles
to (0,pi/4) selects infinitely many distinct relabeling orbits. This consequence
uses the overlap multiset invariant, not the defective literal criterion (24). -/
theorem infinitely_many_steering_classes :
    (∀ theta : ℝ, 0 < theta → theta < Real.pi / 4 →
      IsNormalized (angleAssemblage theta) ∧ IsPureOrthogonal (angleAssemblage theta) ∧
      ¬ HasFiniteLHSModel (angleAssemblage theta)) ∧
    (∀ theta eta : ℝ, 0 < theta → theta < Real.pi / 4 →
      0 < eta → eta < Real.pi / 4 → theta ≠ eta →
      ¬ SteeringConverts (angleAssemblage theta) (angleAssemblage eta) ∧
      ¬ SteeringConverts (angleAssemblage eta) (angleAssemblage theta)) ∧
    Set.Infinite (Set.range (fun theta : {t : ℝ // 0 < t ∧ t < Real.pi / 4} =>
      angleAssemblage theta.val)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
