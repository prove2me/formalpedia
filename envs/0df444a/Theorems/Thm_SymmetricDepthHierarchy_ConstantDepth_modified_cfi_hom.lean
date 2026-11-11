-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_modified_cfi_hom
-- name    : SymmetricDepthHierarchy.ConstantDepth.modified_cfi_hom
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:32.580747+00:00
-- url     : https://prove2.me/theorems/a9ff971c-864f-4442-9ea6-144b1683824c
-- title:
--   Lemma B.20: $\mathrm{hom}(F,\widehat G_0)\ge\mathrm{hom}(F,\widehat G_1)$, strict iff a spanning weak oddomorphism separating the edges of $F$ exists
-- statement:
--   Let $G$ be a connected graph and $F$ a finite graph. Then
--   $$\mathrm{hom}(F,\widehat G_0)\ge\mathrm{hom}(F,\widehat G_1),$$
--   with strict inequality if and only if there exist a subgraph $F'$ of $F$ with $V(F')=V(F)$ and a weak oddomorphism $\varphi:F'\to G$ such that $\varphi(a)\ne\varphi(b)$ for all $ab\in E(F)$.
--
--   The modified CFI graphs detect weak oddomorphisms from spanning subgraphs, which is what allows non-induced minors in Theorem 3.7.
--
--   Differences from the source:
--   - encoding: G_1: the CFI graph G_W for W of odd total weight (well defined up to isomorphism) → G_1 := G_W with W = indicator of an arbitrary vertex v₀ (statement for every v₀); reason: up to isomorphism G_W depends only on ∑ W [Rob26, Cor. 3.7]; every choice of v₀ is one representative
--   - encoding: a subgraph F′ of F with V(F′) = V(F) → a simple graph F′ on the vertex type of F with F′ ≤ F; reason: a spanning subgraph is exactly a subgraph on the same vertex set
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 37 (PDF p. 40), Lemma B.20

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Oddomorphism
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_CFI

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Lemma B.20, printed p. 37 (PDF p. 40). Let `G` be a connected graph and `F` a graph. Then
`hom(F, Ĝ₀) ≥ hom(F, Ĝ₁)`, with strict inequality if and only if there exist a subgraph `F'` of `F`
with `V(F') = V(F)` and a weak oddomorphism `φ : F' → G` such that `φ(a) ≠ φ(b)` for all
`ab ∈ E(F)`. Here `Ĝ₁` is built from the odd twist at an arbitrary vertex `v₀`. -/
theorem modified_cfi_hom {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (v₀ : V) {X : Type} [Fintype X] (F : SimpleGraph X) :
    homCount F (cfiHat G (twist1 v₀)) ≤ homCount F (cfiHat G twist0) ∧
      (homCount F (cfiHat G (twist1 v₀)) < homCount F (cfiHat G twist0) ↔
        ∃ (F' : SimpleGraph X) (φ : F' →g G),
          F' ≤ F ∧ IsWeakOddomorphism φ ∧ ∀ a b, F.Adj a b → φ a ≠ φ b) := by sorry

end SymmetricDepthHierarchy.ConstantDepth
