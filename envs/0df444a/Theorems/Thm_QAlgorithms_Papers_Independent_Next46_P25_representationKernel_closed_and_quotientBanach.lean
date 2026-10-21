-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P25_representationKernel_closed_and_quotientBanach
-- name    : QAlgorithms.Papers.Independent.Next46.P25.representationKernel_closed_and_quotientBanach
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:02:54.805522+00:00
-- url     : https://prove2.me/theorems/825b2176-30ad-4799-99af-1362632c6f83
-- title:
--   Closed kernel, Banach Lie quotient, and induced faithful representation
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $\mathfrak g$ be a Banach Lie algebra, and let $V$ be a Hausdorff topological $\mathbb K$-vector space. Let $\rho:\mathfrak g\to\operatorname{End}_{\mathbb K}(V)$ be a strongly continuous algebraic representation. Its kernel is the actual Lie ideal $\ker\rho=\{x:\rho(x)=0\}$. Then
--
--   $$
--   \ker\rho\text{ is closed},\qquad \mathfrak g/\ker\rho\text{ is a Banach Lie algebra}.
--   $$
--
--   The quotient is the computed algebraic quotient with its usual quotient topology and quotient norm: that norm is definite, the quotient is complete, and its inherited bracket is continuous. This justifies passing to a faithful quotient representation; it does not assert that the period subgroup of Theorem 6.12 automatically stays discrete.
--
--   The induced representation $\overline\rho:\mathfrak g/\ker\rho\to\operatorname{End}_{\mathbb K}(V)$ is also included: it is injective, strongly continuous and bracket preserving, and $\overline\rho(x+\ker\rho)=\rho(x)$ for every $x$. The representative identity fixes the induced action from the given one.
-- source:
--   On Analytic Vectors for Unitary Representations of Infinite Dimensional Lie Groups, arXiv:1002.4792v2, PDF p. 25, Remark 6.13

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P25

noncomputable section

open Set Filter Topology

open scoped Classical ENNReal

namespace QAlgorithms.Papers.Independent.Next46.P25

universe u v w z

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Remark 6.13, PDF p.25: the actual algebraic kernel is a closed
    ideal. Its computed quotient has definite standard quotient norm, is
    complete, and carries the inherited continuous Lie bracket and faithful
    strongly continuous representation. Both descend from the given data;
    their identities on representatives fix them on every quotient class. -/
theorem representationKernel_closed_and_quotientBanach
    {K : Type u} [RCLike K]
    {g : Type v} [NormedAddCommGroup g] [NormedSpace K g] [CompleteSpace g]
    {V : Type w} [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V] [T2Space V]
    (b : ContinuousLieBracket K g)
    (rho : g →ₗ[K] Module.End K V)
    (hLie : ∀ (x y : g) (v : V),
      rho (b.bracket x y) v = rho x (rho y v) - rho y (rho x v))
    (hStrong : StronglyContinuous (fun x v => rho x v)) :
    (∀ (x y : g), y ∈ rho.ker → b.bracket x y ∈ rho.ker) ∧
    IsClosed (rho.ker : Set g) ∧
    (let Q := g ⧸ rho.ker
     CompleteSpace Q ∧ (∀ z : Q, ‖z‖ = 0 → z = 0) ∧
       ∃ (quotientBracket : ContinuousLieBracket K Q)
         (quotientRho : Q →ₗ[K] Module.End K V),
         (∀ x y : g,
           quotientBracket.bracket (rho.ker.mkQ x) (rho.ker.mkQ y) =
             rho.ker.mkQ (b.bracket x y)) ∧
         (∀ x : g, quotientRho (rho.ker.mkQ x) = rho x) ∧
         Function.Injective quotientRho ∧
         (∀ (x y : Q) (v : V),
           quotientRho (quotientBracket.bracket x y) v =
             quotientRho x (quotientRho y v) - quotientRho y (quotientRho x v)) ∧
         StronglyContinuous (fun x v => quotientRho x v)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P25

end
