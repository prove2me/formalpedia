-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P59_affineKernelDichotomy
-- name    : QAlgorithms.Papers.Independent.Information100.P59.affineKernelDichotomy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:28:22.705651+00:00
-- url     : https://prove2.me/theorems/1a7cc232-cd46-4c49-b6de-24bbbd8a1b99
-- title:
--   Lemma 3.17: Affine-kernel dichotomy
-- statement:
--   Let $V$ be a finite-dimensional real vector space and $\mathfrak h\subseteq\mathfrak{gl}(V)\ltimes V$ an affine Lie algebra. Its matrix projection is $\mathfrak l=\{A:\exists b,(A,b)\in\mathfrak h\}$, and its translation kernel is $T=\{t:(0,t)\in\mathfrak h\}$. The kernel $T$ is an $\mathfrak l$-invariant linear subspace. If $I\in\mathfrak l$ and $V$ is a nonzero irreducible $\mathfrak l$-module, exactly one alternative holds:
--
--   $$T=V,\quad\text{or}\quad T=0\ \text{and}\ \mathfrak h=\{(A,Av):A\in\mathfrak l\}\ \text{for some }v\in V.$$
--
--   In the second case every affine field in $\mathfrak h$ fixes $-v$. If the fields have no common fixed point, then $T=V$.
--
--   The projection and kernel are computed from $\mathfrak h$, and the vector $v$ is produced by the conclusion.
-- source:
--   Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control, arXiv:2610.00046v1, PDF p. 16, Lemma 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF p.16, Lemma 3.17. h is an arbitrary affine Lie
subalgebra, supplied as a linear subspace closed under the actual affine bracket.
The translation kernel and matrix projection are computed from h, never supplied independently. -/
theorem affineKernelDichotomy {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (h : Submodule ℝ (Module.End ℝ V × V))
    (hbracket : ∀ X ∈ h, ∀ Y ∈ h, affineBracket X Y ∈ h) :
    (∀ (A : Module.End ℝ V), (∃ b, (A,b) ∈ h) →
      ∀ t : V, (0,t) ∈ h → (0,A t) ∈ h) ∧
    ((∃ b : V, (1,b) ∈ h) → IrreducibleProjection h →
      (Xor (∀ t : V, (0,t) ∈ h)
        ((∀ t : V, (0,t) ∈ h ↔ t = 0) ∧
          ∃ v : V,
            (∀ (A : Module.End ℝ V) (b : V),
              (A,b) ∈ h ↔ (∃ c : V, (A,c) ∈ h) ∧ b = A v) ∧
            (∀ X ∈ h, X.1 (-v) + X.2 = 0))) ∧
      ((¬ ∃ w : V, ∀ X ∈ h, X.1 w + X.2 = 0) → ∀ t : V, (0,t) ∈ h)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P59

end
