-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P24_normal_decomposition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P24.normal_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:55:24.144026+00:00
-- url     : https://prove2.me/theorems/3eedec6c-8426-416c-a959-1d4945c501b3
-- title:
--   Normal-operator decomposition with explicit closedness correction
-- statement:
--   Let $H$ be an arbitrary complex Hilbert space, and let $T$ be a closed densely defined linear operator on $H$ satisfying $T^*T=TT^*$, with equality of domains and actions. There exist everywhere-defined bounded linear operators $A,B$ on $H$ such that
--
--   $$
--   A\text{ is injective},\qquad T=A^{-1}B,\qquad AB=BA,
--   $$
--
--   and $A$ is self-adjoint and $B$ is normal. Moreover,
--
--   $$
--   T=T^*\quad\Longrightarrow\quad B=B^*.
--   $$
--
--   Here $A^{-1}$ is defined on the range of $A$, and $T=A^{-1}B$ is equality of partially defined operators, including their domains. No bounded inverse or surjectivity of $A$ is asserted. This decomposition connects an unbounded normal operator to commuting bounded operators.
--
--   **Source correction.** Closedness is an additional substantive hypothesis omitted from printed Definition 2.1 but used in the proof on pages 2–3. The statement uses this explicitly corrected reading.
-- source:
--   Decomposition of Normal Operators and Its Application to Spectral Theorem, arXiv:2006.04644v2, PDF p. 1, Theorem 1.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P24

noncomputable section

attribute [local instance] Classical.propDecidable

open Set MeasureTheory

open scoped Topology

open QAlgorithms.Papers.Independent.Claimed50.P05

namespace QAlgorithms.Papers.Independent.Intakenext100.P24

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Theorem 1.1, PDF p.1, with clauses (i)–(iii) from Theorem A;
proof on PDF pp.2–3. Equality is equality of actual operator graphs.
Source correction requiring independent moderation:
Printed: Definition 2.1 assumes only a dense domain and T*T = TT*.
Changed: require T also to be closed, as encoded by the accepted Normal.
Why: the proof invokes Theorem 2.2 for closed operators and explicitly uses
closedness. Identity restricted to c00 in l2 is a counterexample to the
literal printed definition. The extra hypothesis is substantive. -/
theorem normal_decomposition (T : Relation H) (hT : Normal (k := ℂ) T) :
    ∃ A B : H →L[ℂ] H,
      InjectiveOperator (boundedGraph A) ∧
      T = mul (inverse (boundedGraph A)) (boundedGraph B) ∧
      mul (boundedGraph A) (boundedGraph B) = mul (boundedGraph B) (boundedGraph A) ∧
      SelfAdjoint (k := ℂ) (boundedGraph A) ∧
      Normal (k := ℂ) (boundedGraph B) ∧
      (SelfAdjoint (k := ℂ) T → SelfAdjoint (k := ℂ) (boundedGraph B)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P24

end
