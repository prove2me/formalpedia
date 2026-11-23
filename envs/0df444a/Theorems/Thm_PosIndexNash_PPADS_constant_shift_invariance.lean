-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_constant_shift_invariance
-- name    : PosIndexNash.PPADS.constant_shift_invariance
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:30.438603+00:00
-- url     : https://prove2.me/theorems/fdcaea71-f14c-4347-bbbb-a4407d2e7235
-- title:
--   A common constant payoff shift preserves nondegeneracy, Nash equilibria and Shapley indices (§3.1)
-- statement:
--   Adding the same real constant $c$ to every entry of both payoff matrices of an $m\times n$ bimatrix game preserves (i) nondegeneracy, (ii) the Shapley index assigned to every strategy pair, and (iii) Nash equilibrium of every pair of mixed strategies. More precisely, the transformed game is nondegenerate iff the original is; the two Shapley-index functions are literally equal; and for $x\in\Delta_m,y\in\Delta_n$, $(x,y)$ is an equilibrium after the shift iff it was one before. This covers the two claims in eq. (2) used in the first normalization step of Theorem 3.2.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p.14, proof of Theorem 3.2, §3.1: "This transformation preserves the set of Nash equilibria and their indices (adding $c$ to all entries adds $c$ to every pure-strategy payoff, which does not change best responses, and leaves the bordered determinants in (1) unchanged). Nondegeneracy is preserved, since the best-response conditions in Definition 2.2 are unchanged." The best-response equations are eq. (2), p.12, and the index is eq. (1), p.13.

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex
import Definitions.Def_PosIndexNash_PPADS_Nondegenerate
import Definitions.Def_QuasiStrictNE_IsNE

theorem PosIndexNash.PPADS.constant_shift_invariance {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) :
    (Nondegenerate (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) ↔
      Nondegenerate A B) ∧
    (∀ x y, shapleyIndex (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) x y =
      shapleyIndex A B x y) ∧
    (∀ x y, x ∈ stdSimplex ℝ (Fin m) → y ∈ stdSimplex ℝ (Fin n) →
      (QuasiStrictNE.IsNE (A + Matrix.of fun _ _ => c) (B + Matrix.of fun _ _ => c) x y ↔
        QuasiStrictNE.IsNE A B x y)) := by sorry
