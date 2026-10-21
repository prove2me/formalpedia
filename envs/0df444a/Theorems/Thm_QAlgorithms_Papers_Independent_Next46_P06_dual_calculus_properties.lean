-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_dual_calculus_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P06.dual_calculus_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:44:01.79092+00:00
-- url     : https://prove2.me/theorems/c4407a5a-2d0e-4091-9157-612152f6980a
-- title:
--   Theorem 8.1
-- statement:
--   Let $\Phi:F\to\mathcal C(X)$ be a proto-calculus on a complex Banach space and a unital complex algebra. Let $B=\operatorname{bdd}(F,\Phi)$, and construct the dual calculus $\Phi'$ on $F'=\langle B^{\mathrm{op}},F^{\mathrm{op}},\Phi'|_{B^{\mathrm{op}}}\rangle$ by extending the bounded Banach transposes. For $f\in F'$ put $D_f=\operatorname{span}\{\Phi(e)x:x\in X,\ e\in B,fe\in B\}$. Then $D_f$ is dense and contained in $\operatorname{dom}\Phi(f)$, so $\Phi(f)$ is densely defined. Moreover,
--
--   $$\Phi(f)'\subseteq\Phi'(f),\qquad \Phi(f)'=\Phi'(f)\iff D_f\text{ is a graph core for }\Phi(f).$$
--
--   The two evaluations are bounded simultaneously; when bounded, $\Phi'(f)=\Phi(f)'$. The transpose is complex linear, not a Hilbert adjoint. The constructed dual calculus can be unbounded, correcting the printed bounded codomain.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 20, Theorem 8.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Theorem 8.1, PDF pp.20–21: density, transpose inclusion with exact core
criterion, and boundedness equivalence. Printed dual codomain L(X') is changed
to C(X'): its canonical extension is possibly unbounded. Why: the extension
construction and clauses (b),(c) require that range. This correction requires
independent moderation. D in (a) means the displayed D_f. -/
theorem dual_calculus_properties [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (f : F) (hf : f ∈ dualDomain Phi) :
    Dense (dualRangeSpan Phi f) ∧ dualRangeSpan Phi f ⊆ graphDomain (Phi f) ∧
    Dense (graphDomain (Phi f)) ∧
    transposeGraph (Phi f) ⊆ dualEvaluation Phi f ∧
    ((transposeGraph (Phi f) = dualEvaluation Phi f) ↔ GraphCore (Phi f) (dualRangeSpan Phi f)) ∧
    (Bounded (Phi f) ↔ Bounded (dualEvaluation Phi f)) ∧
    (Bounded (Phi f) → dualEvaluation Phi f = transposeGraph (Phi f)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
