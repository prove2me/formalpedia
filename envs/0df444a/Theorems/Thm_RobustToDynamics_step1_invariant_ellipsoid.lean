-- Prove2me | Theorems.Thm_RobustToDynamics_step1_invariant_ellipsoid
-- name    : RobustToDynamics.step1_invariant_ellipsoid
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:08.818149+00:00
-- url     : https://prove2.me/theorems/fe64c065-666f-4a6a-9cb7-b4fbee4c80df
-- title:
--   Step 1 — the sets $E(\alpha)$ are bounded and invariant under $x\mapsto Gx$
-- statement:
--   Let $G$ and $M$ be real $n\times n$ matrices with $G^TMG-M=-I$ and $M\succ0$. Then every set
--   $$
--   E(\alpha)=\{x\in\mathbb R^n : x^TMx\le\alpha\}
--   $$
--   is bounded, and for every $\alpha$: if $x\in E(\alpha)$ then $Gx\in E(\alpha)$, and $G^kx\in E(\alpha)$ for every integer $k\ge0$.
--
--   These invariant ellipsoids are what make finite convergence possible: once a trajectory enters an invariant ellipsoid contained in $P$, it never leaves $P$.
--
--   Differences from the source:
--   - generalization: α ≥ 0 → every real α; reason: for α < 0 the set is empty and both claims are trivial; the source's α ≥ 0 is a special case
--   - generalization: M the Lyapunov solution for G with ρ(G) < 1 → any M ≻ 0 with GᵀMG − M = −I; reason: under ρ(G) < 1 the Lyapunov solution satisfies both hypotheses (Step 1); nothing else is used
--   - generalization: rational data → real data; reason: the statement for real matrices specializes to rational ones by casting
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 1, p.14

import Mathlib
import Definitions.Def_RobustToDynamics_ellipsoid

open Matrix

namespace RobustToDynamics

/-- **Step 1: the sets `E(α)` are bounded and invariant under `x ↦ Gx`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 1, p.14: "Since M ≻ 0, the sets E(α) := {x ∈ Rn| xT Mx ≤ α} are bounded for all α ≥ 0.
Furthermore, because GT MG ≺ M in view of (2.14), if x ∈ E(α) for some α ≥ 0, then Gx ∈ E(α), and
hence Gkx ∈ E(α) for all integers k ≥ 0."

Let `M ≻ 0` solve `GᵀMG − M = −I`. Then every `E(α)` is bounded, and `x ∈ E(α)` implies
`Gx ∈ E(α)` and `Gᵏx ∈ E(α)` for every `k ≥ 0`.

**Formalization Note.** Stated for every real `α` (a generalization of `α ≥ 0`; for `α < 0` the set
is empty). `ℝⁿ` is `Fin n → ℝ`, bounded in its (sup-norm) bornology, which agrees with the
Euclidean one. `M ≻ 0` is `Matrix.PosDef`. -/
theorem step1_invariant_ellipsoid {n : ℕ} (G M : Matrix (Fin n) (Fin n) ℝ)
    (hL : Gᵀ * M * G - M = -1) (hM : M.PosDef) :
    (∀ α : ℝ, Bornology.IsBounded (ellipsoid M α)) ∧
      ∀ α : ℝ, ∀ x ∈ ellipsoid M α,
        G *ᵥ x ∈ ellipsoid M α ∧ ∀ k : ℕ, (G ^ k) *ᵥ x ∈ ellipsoid M α := by sorry

end RobustToDynamics
