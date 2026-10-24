-- Prove2me | Theorems.Thm_WernerExt_TwoSided_hamW_casimir
-- name    : WernerExt.TwoSided.hamW_casimir
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:26.809626+00:00
-- url     : https://prove2.me/theorems/02328692-2103-46f2-94ba-705ba5421be2
-- title:
--   Eq. (5), p. 2 (= SM Eq. (7)) — H_W = (C_AB − C_A − C_B)/(2 n_A n_B) + 𝟙/d
-- statement:
--   Let $d\ge2$, $n_A,n_B\ge1$. Let $C_A$, $C_B$, $C_{AB}$ be the quadratic Casimir operators of $SU(d)$ in the $n_A$-, $n_B$- and $(n_A+n_B)$-fold tensor products of the defining representation, acting on Alice's subsystem, Bob's subsystem and the whole system. Then
--   $$H^W=\frac{1}{n_An_B}\sum_{i\in L,\,j\in R}F_{ij}=\frac{1}{2n_An_B}\left(C_{AB}-C_A-C_B\right)+\frac{\mathbb 1}{d}.$$
--
--   This converts the ground state problem of $H^W$ into a problem about Casimir eigenvalues on irreducible subspaces.
--
--   **Formalization Note** $C_n=\sum_{\alpha,\beta}(\sum_iS^{\alpha\beta}_i)(\sum_jS^{\beta\alpha}_j)$ (SM Eq. (5)); $C_{AB}$ is defined on $n_A+n_B$ sites and transported to the joint carrier with Alice's sites first (`Fin.appendEquiv`).
--
--   Differences from the source:
--   - encoding: C_AB on the (n_A + n_B)-fold product → casimirOn d (nA + nB) reindexed along Fin.appendEquiv to (Fin nA → Fin d) × (Fin nB → Fin d); reason: Lean carrier convention; same operator
-- source:
--   Jakab, Solymos, Zimborás, Extendibility of Werner States, arXiv:2208.13743v2, p. 2, Eq. (5); Supplemental Material pp. 1–2 (PDF 7–8), SM Eqs. (5)–(7)

import Mathlib
import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- Eq. (5), p. 2 (= SM Eq. (7)): `H_W = (C_AB − C_A − C_B)/(2 nA nB) + 𝟙/d`. -/
theorem hamW_casimir (d nA nB : ℕ) (hd : 2 ≤ d) (hA : 1 ≤ nA) (hB : 1 ≤ nB) :
    hamW d nA nB =
      ((2 * (nA : ℂ) * (nB : ℂ))⁻¹) •
          (casimirAB d nA nB - casimirA d nA nB - casimirB d nA nB) +
        ((d : ℂ)⁻¹) • (1 : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ) := by sorry

end WernerExt.TwoSided
