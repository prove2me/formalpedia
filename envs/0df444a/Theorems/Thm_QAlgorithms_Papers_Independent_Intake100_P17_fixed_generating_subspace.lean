-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P17_fixed_generating_subspace
-- name    : QAlgorithms.Papers.Independent.Intake100.P17.fixed_generating_subspace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:26:48.992573+00:00
-- url     : https://prove2.me/theorems/bf326fa1-879a-483c-8b9d-5cca5a396242
-- title:
--   Invariant generating subspace is pointwise fixed
-- statement:
--   Let \(G\) be a topological group with continuous involutive automorphism \(\tau\), and let \(\pi\) be a strongly continuous unitary representation of \(G\rtimes\{1,\tau\}\) on a complex Hilbert space \(E\). Write \(\theta=\pi(\tau)\). Let \(S\subseteq G\) satisfy \(1\in\overline S\), let \(F\subseteq E\) be a closed complex linear subspace, and put \(E_+=\overline{\operatorname{span}\pi(S)F}\). If \(E_+\) is \(\theta\)-positive, then
--   \[
--   F\subseteq E_+,\qquad
--   \theta(F)\subseteq F\ \Longleftrightarrow\ (\forall v\in F)\ \theta v=v.
--   \]
--   Here positivity uses the source's inner product, linear in the first variable, on arbitrary vectors.
--
--   Thus invariance and pointwise fixation of the closed generating subspace are equivalent in this reflection-positive setting.
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, PDF p. 10, Remark 1.10: fixed generating subspace

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Remark 1.10, PDF p. 10: 1 is in the closure of S (the printed overbar is essential).
Theta-invariance of the closed generating subspace is equivalent to pointwise fixation. -/
theorem fixed_generating_subspace
    {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (tau : G ≃* G) (htau : Function.Involutive tau) (htaucont : Continuous tau)
    (R : ReflectionAction G tau E) (hcont : ∀ v, Continuous (fun g => R.pi g v))
    (S : Set G) (hone : (1 : G) ∈ closure S)
    (F : Submodule ℂ E) (hclosed : IsClosed (F : Set E))
    (hpos : ThetaPositive R.theta (orbitSpan R S F)) :
    F ≤ orbitSpan R S F ∧
      ((∀ v ∈ F, R.theta v ∈ F) ↔ ∀ v ∈ F, R.theta v = v) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P17

end
