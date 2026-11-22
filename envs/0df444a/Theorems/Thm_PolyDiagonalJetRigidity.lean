-- Prove2me | Theorems.Thm_PolyDiagonalJetRigidity
-- name    : PolyDiagonalJetRigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:52.903749+00:00
-- url     : https://prove2.me/theorems/166b49dd-7afb-4f18-8bff-682d3b15e340
-- title:
--   Poly Diagonal Jet Rigidity: Poly Diagonal Jet Rigidity
-- statement:
--   Rigidity for polynomial functions on the plane: a smooth `S` whose `(k+1)`-st derivative
--   vanishes identically and whose DIAGONAL jets at the origin all vanish up to order `k` is itself
--   identically zero.
--
--   The condition `D^{k+1} S == 0` says exactly that `S` is a polynomial function of degree at most
--   `k`; only the stated form of the condition is used.  Vanishing is assumed only on the DIAGONAL
--   `D^j S(0)[w, ..., w]`, which is all pm-0014's jet layer ever carries, and it is all the proof
--   needs: the Taylor expansion along the ray `s |-> s w` sees exactly the diagonal evaluations.
--
--   This is the shared rigidity step of `PolyInverseEstimate`, used there twice -- once to make the
--   jet map `S |-> (D^0 S(0), ..., D^k S(0))` injective, and once to make the sup-norm over the closed
--   unit ball definite on the space of such `S`.  Those two uses are what make it a statement rather
--   than a step: a node exposing only one of its consequences would leave the other without it.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PolyDiagonalJetRigidity.lean#L16-L56
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PolyDiagonalJetRigidity.lean#L16-L56

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_PolyDiagonalJetRigidity
import Theorems.Thm_IteratedDerivAlongRay

set_option autoImplicit false

theorem PolyDiagonalJetRigidity (k : ℕ) (S : Plane → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (htop : ∀ w : Plane, iteratedFDeriv ℝ (k + 1) S w = 0)
    (hjets : ∀ j : ℕ, j ≤ k → ∀ w : Plane, iteratedFDeriv ℝ j S 0 (fun _ => w) = 0) :
    S = 0 := by sorry
