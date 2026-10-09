-- Prove2me | Theorems.Thm_RestartPD_Fixed_prop_8
-- name    : RestartPD.Fixed.prop_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:56.572165+00:00
-- url     : https://prove2.me/theorems/db4e375d-cb14-4468-887b-5096e881698e
-- title:
--   Proposition 8, p. 17 — under Property 3, ‖z̄ᵗ − z⁰‖ = 0 forces z̄ᵗ ∈ Z⋆
-- statement:
--   Assume the standing assumptions of (1) and let the base algorithm satisfy Property 3 with constants $q, C$. Let $z^0 \in Z$, let $\{\bar z^t\}$ be an output sequence of the algorithm started at $z^0$, and let $t \ge 1$. If
--   $$\|\bar z^t - z^0\| = 0, \quad\text{then}\quad \bar z^t \in Z^\star.$$
--
--   This removes the degenerate case $r = 0$, where sharpness (defined only for $r > 0$) says nothing, from the proofs of Theorems 1 and 2.
--
--   **Formalization Note** The page concludes "$\bar z^{n,t} = z^{n,0} \in Z^\star$". With a semi-norm, $\|\bar z^t - z^0\| = 0$ does not give $\bar z^t = z^0$; what the proof establishes and what Theorem 1 uses is $\bar z^t \in Z^\star$, which is what is stated.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 17, Proposition 8

import Mathlib
import Definitions.Def_RestartPD_Fixed_Algorithms

namespace RestartPD.Fixed

/-- Proposition 8, p. 17: under Property 3, if `‖z̄ᵗ − z⁰‖ = 0` for an output `z̄ᵗ` (`t ≥ 1`) of a
run from `z⁰ ∈ Z`, then `z̄ᵗ ∈ Z⋆`. (The page also writes `z̄ᵗ = z⁰`, which a semi-norm does not
give; only the membership is stated.) -/
theorem prop_8 {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hP : IsPDProblem L X Y) (p : Seminorm ℝ (E n m))
    (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) (h3 : Property3 L X Y p Runs q C)
    (z0 : E n m) (hz0 : z0 ∈ X ×ˢ Y) (zb : ℕ → E n m) (hzb : zb ∈ Runs z0)
    (t : ℕ) (ht : 1 ≤ t) (hzero : p (zb t - z0) = 0) :
    zb t ∈ Zstar L X Y := by sorry

end RestartPD.Fixed
