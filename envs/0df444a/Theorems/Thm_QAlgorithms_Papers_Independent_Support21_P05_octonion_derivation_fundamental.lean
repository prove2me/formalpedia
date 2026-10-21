-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P05_octonion_derivation_fundamental
-- name    : QAlgorithms.Papers.Independent.Support21.P05.octonion_derivation_fundamental
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:33:15.684974+00:00
-- url     : https://prove2.me/theorems/2cda6424-49b9-4c48-a93f-63674b8a1c98
-- title:
--   Octonion derivations and the fundamental seven-dimensional action
-- statement:
--   All spaces and maps are complex-linear, and composition conjugation fixes the base field. Let $\mathbb O$ be the complex octonions in the Zorn coordinates of (3.3), with negative diagonal dot contraction and positive cross terms. Put $\mathbb O_0=\{(\alpha^+,\alpha^-,v^+,v^-):\alpha^++\alpha^-=0\}$. For $a\in\mathfrak{sl}_3(\mathbb C)$ and vectors $A^+,A^-$, define
--
--   $$
--   \delta_{a,A^+,A^-}(\alpha^+,\alpha^-,v^+,v^-)=\bigl(s,-s,\ av^++(\alpha^--\alpha^+)A^+-A^-\wedge v^-,\ -v^-a-(\alpha^--\alpha^+)A^--A^+\wedge v^+\bigr),
--   \quad s=-v^-\cdot A^++A^-\cdot v^+.
--   $$
--
--   Each such map is a derivation of the octonion product: $\delta(xy)=\delta(x)y+x\delta(y)$. Conversely, every complex-linear octonion derivation is obtained from exactly one triple $(a,A^+,A^-)$. With the special bracket (4.5), these maps satisfy
--
--   $$\delta_{[u,v]_Z}=\delta_u\delta_v-\delta_v\delta_u.$$
--
--   They annihilate all scalar octonions $(r,r,0,0)$, and their images have trace zero. The space $\mathbb O_0$ has complex dimension seven, and its only complex subspaces invariant under all these maps are $0$ and $\mathbb O_0$. Thus the restricted action is the fundamental irreducible $7$, and the action identifies all octonion derivations.
--
--   This distinguishes the seven-dimensional action from the adjoint Zorn realization and keeps the ordinary contractions in (4.10) separate from the negative contraction in (3.3).
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs Part 2: Zorn-type Representations, arXiv:1403.5120v2, PDF p. 12, (4.10): derivation action and fundamental 7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P05

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

/-- (4.10), PDF pp. 9–12: this action is exactly all complex octonion derivations,
preserves the traceless seven-space, satisfies the representation identity and is
irreducible on that space (the fundamental 7). Scalar matrices are fixed. -/
theorem octonion_derivation_fundamental :
    (∀ a : G2Coordinates, ∀ x y : Octonions,
      octonionAction (g2Value a) (octonionMul x y) =
        octonionMul (octonionAction (g2Value a) x) y +
        octonionMul x (octonionAction (g2Value a) y)) ∧
    (∀ D : Octonions →ₗ[ℂ] Octonions,
      (∀ x y, D (octonionMul x y) = octonionMul (D x) y + octonionMul x (D y)) →
      ∃! a : G2Coordinates, ∀ z, D z = octonionAction (g2Value a) z) ∧
    (∀ a b : G2Coordinates, ∀ z,
      octonionAction (g2Bracket (g2Value a) (g2Value b)) z =
        octonionAction (g2Value a) (octonionAction (g2Value b) z) -
        octonionAction (g2Value b) (octonionAction (g2Value a) z)) ∧
    (∀ a : G2Coordinates, ∀ z, octonionTrace (octonionAction (g2Value a) z) = 0) ∧
    (∀ a : G2Coordinates, ∀ r : ℂ, octonionAction (g2Value a) (r, r, 0, 0) = 0) ∧
    Module.finrank ℂ TracelessOctonions = 7 ∧
    (∀ S : Submodule ℂ Octonions, S ≤ TracelessOctonions →
      (∀ a : G2Coordinates, ∀ z ∈ S, octonionAction (g2Value a) z ∈ S) →
      S = ⊥ ∨ S = TracelessOctonions) := by sorry

end QAlgorithms.Papers.Independent.Support21.P05

end
