-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_label_isometry
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.label_isometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:07:28.290226+00:00
-- url     : https://prove2.me/theorems/691782f5-cbb0-4d8e-8cc6-33f930a3c3ee
-- title:
--   Reversible local extraction of the canonical label
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   There is a finite computational register representing $Y$, a local isometry $V:AC\to ACY$, and a CPTP map $R:ACY\to AC$ such that, for every supported $x$,
--   $$V(|\psi_x\rangle|\sigma_x\rangle)=|\psi_x\rangle|\sigma_x\rangle|y(x)\rangle,$$
--   $$R\!\left(V|\psi_x\sigma_x\rangle\langle\psi_x\sigma_x|V^\dagger\right)=|\psi_x\sigma_x\rangle\langle\psi_x\sigma_x|.$$
--
--   The canonical extension and original source are equivalent by local operations of Alice. Reversibility is asserted on the ensemble, without requiring an inverse identity on every state of $ACY$.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 2, Equation (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Equation (3) and source equivalence, PDF p.2: a source-independent local
isometry records canonical Y and a CPTP local operation reverses it on every
supported letter. No inverse identity on arbitrary ACY states is asserted. -/
theorem label_isometry [Countable X] (s : ProductPureSource X A C) (hs : s.Valid) :
    ∃ m : ℕ, ∃ e : IrreducibleLabel s ≃ Fin (m + 1),
    ∃ V : Matrix ((A × C) × Fin (m + 1)) (A × C) ℂ,
    ∃ R : Superop ((A × C) × Fin (m + 1)) (A × C),
      Accepted.IsIso V ∧ IsChannel R ∧
      (∀ x, WithLp.toLp 2 (V.mulVec (WithLp.ofLp (s.joint x))) =
        tensorVec (s.joint x) (ket (e (s.label x)))) ∧
      (∀ x, R (conjSuperop V (pureDensity (s.joint x))) = pureDensity (s.joint x)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
