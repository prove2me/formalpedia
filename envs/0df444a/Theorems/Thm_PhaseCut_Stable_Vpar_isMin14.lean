-- Prove2me | Theorems.Thm_PhaseCut_Stable_Vpar_isMin14
-- name    : PhaseCut.Stable.Vpar_isMin14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:16.151685+00:00
-- url     : https://prove2.me/theorems/c464d8a1-85b5-47b6-a29c-d51deed9a0b8
-- title:
--   Proof of Theorem 4.7, p. 14 — V^∥_PC minimizes (14) for b = |Ax₀| + b_{n,PL}
-- statement:
--   Let $A \in \mathbb{C}^{n\times p}$, $x_0 \in \mathbb{C}^p$, $s \ge 1$, and let $V_{PC} \in \mathbf{H}_n$ be positive semidefinite. Let $V_{PC}^{/\!/} = AA^\dagger V_{PC} AA^\dagger$ and $b_{n,PL,i} = \sqrt{(V_{PC}^{/\!/})_{ii}} - |Ax_0|_i$ for $i = 1, \dots, n$. Then $V_{PC}^{/\!/}$ is a minimizer of problem (14),
--   $$\text{minimize } \Big(\sum_{i}\big|V_{ii} - b_i^2\big|^s\Big)^{1/s} \quad\text{subject to } V \in \mathbf{H}_n^+ \cap \mathcal{F},$$
--   for $b = |Ax_0| + b_{n,PL}$.
--
--   This is the step of the proof of Theorem 4.7 that turns a PhaseCut solution into a Weak PhaseLift solution for a modified noise vector, to which the assumed stability of Weak PhaseLift is then applied.
--
--   **Formalization Note.** The paper applies this to the minimizer $V_{PC}$ of (13); only $V_{PC} \succeq 0$ is used, and the statement is made for every positive semidefinite $V_{PC}$. The page writes $|Ax_0|_{ii}$ for the $i$-th entry $|Ax_0|_i$. The objective of (14) is the $\ell^s$ distance $d(\operatorname{diag}(V), b^2)$ of p. 11, which the paper identifies with $d_s(V, \mathcal{H}_b)$; diagonal entries are read through their real parts.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Theorem 4.7, p. 14

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder


/-- **`V^∥_PC` minimizes (14)**, proof of Theorem 4.7 (p. 14). For every `V_PC ⪰ 0` and `s ≥ 1`, with
`b_{n,PL,i} = √(V^∥_{PC,ii}) − |Ax₀|ᵢ`, the matrix `V^∥_PC` minimizes (14) for `b = |Ax₀| + b_{n,PL}`. -/
theorem Vpar_isMin14 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (s : ℝ) (hs : 1 ≤ s)
    (x₀ : Fin p → ℂ) (VPC : Matrix (Fin n) (Fin n) ℂ) (hV : VPC.PosSemidef) :
    IsMin14 A s (absAx A x₀ + fun i => Real.sqrt (Vpar A VPC i i).re - absAx A x₀ i)
      (Vpar A VPC) := by sorry
end PhaseCut.Stable
