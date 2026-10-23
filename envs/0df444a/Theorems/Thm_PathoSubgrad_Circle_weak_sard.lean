-- Prove2me | Theorems.Thm_PathoSubgrad_Circle_weak_sard
-- name    : PathoSubgrad.Circle.weak_sard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:22:33.85799+00:00
-- url     : https://prove2.me/theorems/2c0697f6-be07-4b9d-a1a3-b326a6eb6099
-- title:
--   Q1, p. 3 — for i0 large, f satisfies the weak Sard condition
-- statement:
--   Let $\psi$ be any bump profile. For every sufficiently large $i_0$, the function $f$ of (4) satisfies the weak Sard condition (Definition 3): $f$ is constant on each connected component of its critical set $\operatorname{crit}f$.
--
--   In the companion work the weak Sard condition yields several positive results (convergence of the values, criticality of limit points); this example shows that it does not give convergence of the sequence itself.
--
--   **Formalization Note.** The claim is made in the answer to Q1 without a threshold; it rests on $\operatorname{crit}f=S^1\cup\{0\}$ (Proposition 6 (iv)), which is proved for $i_0$ large, so the statement reads $\exists N,\ \forall i_0\ge N$.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, p. 3, Q1

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_PathoSubgrad_Circle_Construction

open Filter Topology
open scoped InnerProductSpace ContDiff

namespace PathoSubgrad.Circle

theorem weak_sard (Ψ : BumpProfile) : ∃ N : ℕ, ∀ i0 ≥ N, WeakSard (fCirc Ψ i0) := by sorry

end PathoSubgrad.Circle
