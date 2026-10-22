-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_multilinearMap_continuous_lift
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.multilinearMap_continuous_lift
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:10:55.894775+00:00
-- url     : https://prove2.me/theorems/ef2ab60e-372b-49c7-8c0e-b329e8eb9792
-- title:
--   Continuity of a multilinear lift through a linear injection
-- statement:
--   Let $n\ge1$, and let $X_1,\ldots,X_n,Y,Z$ be real or complex Banach spaces over the same scalar field. Let $\eta:Y\to Z$ be an injective continuous linear map and $A:X_1\times\cdots\times X_n\to Z$ a continuous multilinear map whose range is contained in $\eta(Y)$. Then there is a unique continuous multilinear map $\widetilde A$ with
--
--   $$\widetilde A:X_1\times\cdots\times X_n\to Y,\qquad \eta\circ\widetilde A=A.$$
--
--   Thus the lift determined by injectivity and range containment is continuous; no closed-range or topological-embedding assumption on $\eta$ is needed.
--
--   **Formalization Note** The printed lemma calls $\eta$ a continuous injection. Its proof uses composition as a linear map between operator spaces, recovering the implicit linearity convention.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 27, Lemma 9.1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

/-- Lemma 9.1, PDF pp. 27–28: lifting a continuous multilinear map
through a continuous linear injection between Banach spaces preserves
continuity. Linearity of eta is implicit in the printed proof. Uniqueness
identifies the map induced by the specified injection. -/
theorem multilinearMap_continuous_lift
    {K : Type u} [RCLike K]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Type v)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace K (X i)]
    [∀ i, CompleteSpace (X i)]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
    {Z : Type z} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (eta : Y →L[K] Z) (hEta : Function.Injective eta)
    (A : ContinuousMultilinearMap K X Z)
    (hRange : ∀ x, ∃ y : Y, eta y = A x) :
    ∃! B : ContinuousMultilinearMap K X Y, ∀ x, eta (B x) = A x := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P22
