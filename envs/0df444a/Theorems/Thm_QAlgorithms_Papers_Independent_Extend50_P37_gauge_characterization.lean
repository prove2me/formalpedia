-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_gauge_characterization
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.gauge_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:19:36.071424+00:00
-- url     : https://prove2.me/theorems/b6e35797-939f-4b98-8a48-76f683f0a121
-- title:
--   III A: equivalent gauge-group definitions and block characterization
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, a unitary subgroup $G$ satisfies $G=G''$ if and only if $G=G_{\mathcal A}$ for a unital adjoint-closed matrix algebra $\mathcal A$. Equivalently it has a physical unitary block presentation
--   $$G\simeq\bigoplus_J(I_{m_J}\otimes U(n_J)),\qquad m_J,n_J>0,\quad\sum_Jm_Jn_J=d.$$
--   Every such embedded block group is gauge, and the multiset of pairs $(m_J,n_J)$ is unique. For every such algebra,
--   $$\operatorname{Comm}(G_{\mathcal A})=\operatorname{Alg}(G_{\mathcal A}')=\mathcal A,\qquad
--   \operatorname{Comm}(G_{\mathcal A}^{\times n})=\operatorname{Alg}((G_{\mathcal A}')^{\times n})=\mathcal A^{\otimes n}.$$
--   This identifies the algebra and its gauge symmetry, preserving the actual embedding and multiplicities. Zero padded blocks are omitted.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 6, III A: equivalent gauge-group definitions and block characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.6-7, III A: equivalent definitions, physical block characterization,
uniqueness of multiplicities, and the two commutant identities (3.1)-(3.2). -/
theorem gauge_characterization [Nonempty I] :
    (∀ G : Set (Mat I), IsGauge G ↔
      ∃ A : StarSubalgebra ℂ (Mat I), G = unitaryCentralizer (A : Set (Mat I))) ∧
    (∀ G : Set (Mat I), IsGauge G ↔ ∃ b : BlockPresentation I, G = b.group) ∧
    (∀ b c : BlockPresentation I, b.group = c.group → b.signature = c.signature) ∧
    (∀ A : StarSubalgebra ℂ (Mat I),
      Set.centralizer (unitaryCentralizer (A : Set (Mat I))) = (A : Set (Mat I)) ∧
      alg (unitaryCentralizer (unitaryCentralizer (A : Set (Mat I)))) = (A : Set (Mat I)) ∧
      ∀ n : ℕ, 0 < n →
        Set.centralizer (localSet n (unitaryCentralizer (A : Set (Mat I)))) = tensorAlg n (A : Set (Mat I)) ∧
        alg (localSet n (unitaryCentralizer (unitaryCentralizer (A : Set (Mat I))))) = tensorAlg n (A : Set (Mat I))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
