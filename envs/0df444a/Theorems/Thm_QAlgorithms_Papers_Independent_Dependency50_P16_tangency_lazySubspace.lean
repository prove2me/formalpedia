-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_tangency_lazySubspace
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.tangency_lazySubspace
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:15:53.774881+00:00
-- url     : https://prove2.me/theorems/e5e8c760-b4af-48cd-93c8-ff67b6f98390
-- title:
--   Lemma 3.4: Tangency forces a lazy subspace
-- statement:
--   Let $F$ be a nonempty coordinate face of $\Delta^{n-1}$, with $d$ supported coordinates, where $1\le d\le n$. Let $\lambda\in\operatorname{relint}F$ and let $A\in\operatorname{conv}\mathcal L$ be a convex combination of induced generators. If $A\lambda$ lies in the linear tangent space of $F$, then
--
--   $$\exists S\subseteq\mathbb C^n:\quad \dim_{\mathbb C}S=d,\qquad V_kS\subseteq S\quad\text{for every }k.$$
--
--   Thus tangency at an interior face point forces a lazy subspace.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 9, Lemma 3.4: Tangency forces a lazy subspace

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

/-- arXiv:2308.00561v1, PDF p.9, Lemma 3.4: Tangency forces a lazy subspace. The face cardinality is d, avoiding truncated affine dimensions. Full and singleton faces are included. -/
theorem tangency_lazySubspace {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (F : Face n) (x : Vec n) (hx : x ∈ faceInterior F) (A : RMat n)
    (hA : A ∈ convexHull ℝ (fields D)) (ht : A *ᵥ x ∈ faceTangent F) :
    ∃ S : Submodule ℂ (Hilbert n), lazy D.jump S ∧ Module.finrank ℂ S = F.support.card := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
