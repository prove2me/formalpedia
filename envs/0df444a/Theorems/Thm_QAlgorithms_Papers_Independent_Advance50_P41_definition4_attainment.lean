-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P41_definition4_attainment
-- name    : QAlgorithms.Papers.Independent.Advance50.P41.definition4_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:08:28.22608+00:00
-- url     : https://prove2.me/theorems/b4b9089c-86c8-486e-82f6-b38d0afbe347
-- title:
--   Attainment and environment bound in Definition 4
-- statement:
--   Let $\mathcal E=\{p(x),|\psi_x\rangle^A\otimes|\sigma_x\rangle^C\}$ be a countably supported ensemble with strictly positive probabilities summing to one and normalized pure vectors on finite-dimensional complex systems $A,C$. Let $Y=y(X)$ be the canonical orthogonal irreducible-component label of the joint $AC$ ensemble. Entropies $S$ use base-two logarithms and refer to the resulting source and its canonical $Y$ extension.
--
--   For an isometry $V:AC\to\widehat A\widehat C W$, let $f(V)$ be the average joint root fidelity of the retained $\widehat A\widehat C$ output, and let $J(V)=I(X:\widehat CW)$, evaluated as the finite-output Holevo entropy difference. Set $D=(\dim A)^2(\dim C)^2$. For each $\epsilon\ge0$, the set of values $J(V)$ with $1\le\dim W\le D$ and $f(V)\ge1-\epsilon$ is nonempty and bounded above, and
--   $$I_\epsilon(\omega)=\max_{V:\,1\le\dim W\le D,\ f(V)\ge1-\epsilon} J(V).$$
--   For every admissible isometry with any larger finite environment, there exists one with environment dimension at most $D$ preserving both $f(V)$ and $J(V)$.
--
--   Thus the dimension-bounded definition attains the unrestricted finite-environment optimization.
-- source:
--   Entanglement-Assisted Quantum Data Compression, arXiv:1901.06346v1, PDF p. 3, Definition 4, following paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P41

open Filter

open scoped Topology BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X A C : Type} [Fintype A] [Fintype C]

/-- Definition 4, PDF p.3: nonempty bounded optimization, actual maximum,
and w.l.o.g. environment compression preserving both fidelity and objective.
All eps>=0 are included; existence of the maximizer is not a hypothesis. -/
theorem definition4_attainment [Countable X] (s : ProductPureSource X A C) (hs : s.Valid)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (extractionValues s eps).Nonempty ∧ BddAbove (extractionValues s eps) ∧
    (∃ V : Extraction A C,
      V.environmentDimension ≤ Fintype.card A ^ 2 * Fintype.card C ^ 2 ∧
      1 - eps ≤ V.fidelity s ∧ V.objective s = extractionInformation s eps) ∧
    (∀ V : Extraction A C, 1 - eps ≤ V.fidelity s →
      ∃ U : Extraction A C,
        U.environmentDimension ≤ Fintype.card A ^ 2 * Fintype.card C ^ 2 ∧
        U.fidelity s = V.fidelity s ∧ U.objective s = V.objective s) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P41

end
