-- Prove2me | Theorems.Thm_RobustToDynamics_step2_outer_ellipsoid
-- name    : RobustToDynamics.step2_outer_ellipsoid
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:38.124164+00:00
-- url     : https://prove2.me/theorems/02edafc9-570a-44d8-b2fd-b845ad67f3bb
-- title:
--   (2.16) — every $x$ with $l\le x\le u$ has $x^TMx\le\alpha_2$, so $P\subseteq E(\alpha_2)$
-- statement:
--   Let $M$ be a real $n\times n$ matrix and $l,u\in\mathbb R^n$, and put
--   $$
--   \alpha_2=\sum_{i=1}^n\sum_{j=1}^n\max\{|M_{ij}u_iu_j|,\ |M_{ij}l_il_j|,\ |M_{ij}u_il_j|,\ |M_{ij}l_iu_j|\}. \tag{2.16}
--   $$
--   Then every $x$ with $l_i\le x_i\le u_i$ for all $i$ satisfies $x^TMx\le\alpha_2$. Consequently every polyhedron $P=\{x: Ax\le b\}$ contained in the box $\{x: l\le x\le u\}$ satisfies $P\subseteq E(\alpha_2)$.
--
--   $E(\alpha_2)$ is the outer ellipsoid of Step 2.
--
--   Differences from the source:
--   - generalization: M the Lyapunov solution; l_i, u_i the LP minima and maxima of x_i over P → any real M; any box bounds l, u; reason: the bound uses neither symmetry nor definiteness of M, and the paper's box is one box containing P
--   - generalization: rational data → real data; reason: the statement for real matrices specializes to rational ones by casting
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 2, display (2.16), p.15

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_RobustToDynamics_ellipsoid
import Definitions.Def_RobustToDynamics_alpha2

open Matrix

namespace RobustToDynamics

/-- **(2.16): the outer ellipsoid `P ⊆ E(α₂)`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 2, display (2.16), p.15: "We can now bound xT Mx = ∑i,j Mi,jxixj term by term to obtain
α2 = ∑∑ max{|Mi,juiuj|, |Mi,jlilj|, |Mi,juilj|, |Mi,jliuj|}. Clearly for any x ∈ P, we have
xT Mx ≤ α2 and therefore P ⊆ E(α2)."

For every real `n × n` matrix `M` and box bounds `l, u ∈ ℝⁿ`: every `x` with `l ≤ x ≤ u`
satisfies `xᵀMx ≤ α₂`; hence every polyhedron `P` inside the box satisfies `P ⊆ E(α₂)`.

**Formalization Note.** The box is `Set.Icc l u` in the componentwise order of `Fin n → ℝ`. `M` is
any real matrix (the bound needs neither symmetry nor definiteness), and `l, u` are any bounds of a
box containing `P` (the paper's coordinatewise LP minima and maxima are one choice). -/
theorem step2_outer_ellipsoid {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (l u : Fin n → ℝ) :
    (∀ x ∈ Set.Icc l u, x ⬝ᵥ (M *ᵥ x) ≤ alpha2 M l u) ∧
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
        polyhedron A b ⊆ Set.Icc l u → polyhedron A b ⊆ ellipsoid M (alpha2 M l u) := by sorry

end RobustToDynamics
