-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_denseCodingIdentities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.denseCodingIdentities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:19:27.74021+00:00
-- url     : https://prove2.me/theorems/92f4a132-16c2-4373-93e7-b4f8a28f5cff
-- title:
--   Copied-frame generalized Bell system and projector resolution
-- statement:
--   Let $A$ be a nonzero finite-dimensional Hilbert space, let $m\ge1$, and let $J:\mathbb C^m\to A$ be an isometry with columns $e_k$ indexed by residues $k\in\mathbb Z_m$. Copy the same frame into Bob's copy of $A$. Put $P=JJ^*$ and $\psi=m^{-1/2}\sum_k e_k\otimes e_k$. On the frame let $Ue_k=e_{k+1}$ and $Ve_k=e^{2\pi i k/m}e_k$, and extend both as the identity on its orthogonal complement. Set $W_{\alpha\beta}=U^\alpha V^\beta$ and $\psi_{\alpha\beta}=(I_B\otimes W_{\alpha\beta})\psi$. Then the $m^2$ vectors are orthonormal, they span $B\otimes A$ when $m=\dim A$, and
--
--   $$\sum_{\alpha,\beta\in\mathbb Z_m}|\psi_{\alpha\beta}\rangle\langle\psi_{\alpha\beta}|=P\otimes P.$$
--
--   This identifies the finite dense-coding system, including proper subspaces. **Formalization Note** The tensor order is Bob first. Replacing the printed labels $1,\ldots,m$ by residues changes individual vectors only by harmless scalar phases.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 3, §II, unnumbered assertions 1)–2): generalized Bell system

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.3, assertions 1)--2): copied-frame Bell system, spanning in the full-rank
case; the projector sum is P tensor P, not the ambient identity in general. -/
theorem denseCodingIdentities {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    {m : ℕ} [NeZero m] (J : Matrix A (ZMod m) ℂ) (hJ : Jᴴ * J = 1) :
    Orthonormal ℂ (frameBell J) ∧
    (m = Fintype.card A → Submodule.span ℂ (Set.range (frameBell J)) = ⊤) ∧
    ∑ x : ZMod m × ZMod m, pureDensity (frameBell J x) =
      Matrix.kronecker (frameProjector J) (frameProjector J) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
