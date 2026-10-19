-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_maximalDecay_subspaceStructure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.maximalDecay_subspaceStructure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:51:25.788249+00:00
-- url     : https://prove2.me/theorems/ad458f6f-f0fc-43ac-9999-786dfcb2c166
-- title:
--   Unnumbered maximal decaying subspace
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, call $S$ decaying when $\operatorname{tr}(P_Se^{tG}\rho)\to0$ for every normalized initial density $\rho$. Decaying subspaces are closed under sums and taking subspaces, and there is a unique greatest one, $D_{\max}$, with
--
--   $$S\text{ decaying}\quad\Longleftrightarrow\quad S\subseteq D_{\max}.$$
--
--   Its orthogonal complement is the unique least asymptotic subspace, where asymptotic means the orthogonal complement is decaying. The maximal space is constructed as the supremum of the concrete decaying family.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 33, Unnumbered maximal decaying subspace

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.33, Unnumbered maximal decaying subspace. Trace limits quantify every initial density. Submodule suprema, rather than real suprema, construct the maximal object. For the zero generator only the zero subspace decays. -/
theorem maximalDecay_subspaceStructure {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    (∀ S T : Submodule ℂ (Hilbert n), decaying D S → decaying D T → decaying D (S ⊔ T)) ∧
    (∀ S T : Submodule ℂ (Hilbert n), decaying D T → S ≤ T → decaying D S) ∧
    decaying D (maximalDecay D) ∧
    (∀ S : Submodule ℂ (Hilbert n), decaying D S ↔ S ≤ maximalDecay D) ∧
    (∃! S : Submodule ℂ (Hilbert n), decaying D S ∧ ∀ T, decaying D T → T ≤ S) ∧
    asymptotic D (minimalAsymptotic D) ∧
    (∀ S : Submodule ℂ (Hilbert n), asymptotic D S → minimalAsymptotic D ≤ S) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
