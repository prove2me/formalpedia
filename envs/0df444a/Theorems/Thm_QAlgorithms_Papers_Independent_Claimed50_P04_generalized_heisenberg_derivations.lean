-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_generalized_heisenberg_derivations
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.generalized_heisenberg_derivations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:48:54.197976+00:00
-- url     : https://prove2.me/theorems/143d1f40-262d-4ec3-b246-9f861d0e005f
-- title:
--   Proposition 3.7
-- statement:
--   Let $V,Z$ be finite-dimensional real vector spaces and $\beta:V\times V\to Z$ an alternating bilinear map with zero left radical. On $V\oplus Z$ use the bracket $[(v,z),(w,t)]=(0,\beta(v,w))$. Every linear derivation $D$ has blocks $D_V,D_{V,Z},D_Z$ satisfying
--   $$D(v,z)=(D_Vv,D_{V,Z}v+D_Zz),\qquad D_Z\beta(v,w)=\beta(D_Vv,w)+\beta(v,D_Vw).$$
--   The diagonal block map is itself a derivation, $D(0,z)=(0,D_Zz)$, and $[D_V,X]$ preserves $\beta$ whenever $X$ does. Derivations are expressed by the Leibniz identity for this exact bracket. This retains all three clauses.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 18, Proposition 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04

namespace QAlgorithms.Papers.Independent.Claimed50.P04

noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section Heisenberg

variable {V Z : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- Proposition 3.7, PDF p. 18: all three clauses, including the diagonal derivation
and invariance of generalized sp under ad(DV). Nondegeneracy is beta's LEFT radical. -/
theorem generalized_heisenberg_derivations (b : V →ₗ[ℝ] V →ₗ[ℝ] Z)
    (halt : ∀ v, b v v = 0) (hnd : ∀ v, (∀ w, b v w = 0) → v = 0)
    (D : Module.End ℝ (V × Z)) (hd : HeisenbergDerivation b D) :
    ∃ DV : Module.End ℝ V, ∃ DVZ : V →ₗ[ℝ] Z, ∃ DZ : Module.End ℝ Z,
      (∀ v z, D (v, z) = (DV v, DVZ v + DZ z)) ∧
      (∀ z, D (0, z) = (0, DZ z)) ∧ BetaCompatiblePair b DV DZ ∧
      HeisenbergDerivation b (diagonalBlocks DV DZ) ∧
      (∀ X : Module.End ℝ V, PreservesForm b X →
        PreservesForm b (DV.comp X - X.comp DV)) := by sorry

end Heisenberg

end

end QAlgorithms.Papers.Independent.Claimed50.P04
