-- Prove2me | Theorems.Thm_PhaseCut_Stable_eq_22
-- name    : PhaseCut.Stable.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:40:32.089833+00:00
-- url     : https://prove2.me/theorems/af02af3f-9fab-4dbd-a895-b150054b5cde
-- title:
--   Bound cited as (22), proof of Lemma A.1, p. 24 — a minimizer V_PC of (13) has Tr V^⊥_PC ≤ ‖b_{n,PC}‖₂²
-- statement:
--   Let $A \in \mathbb{C}^{n\times p}$, $x_0 \in \mathbb{C}^p$, $b_{n,PC} \in \mathbb{R}^n$ and $b = |Ax_0| + b_{n,PC}$. Let $V_{PC}$ be a minimizer of problem (13),
--   $$\text{minimize } d_1(V, \mathcal{F}) \quad\text{subject to } V \in \mathbf{H}_n^+ \cap \mathcal{H}_b,$$
--   and let $V_{PC}^\perp = (I - AA^\dagger)V_{PC}(I - AA^\dagger)$. Then
--   $$\operatorname{Tr} V_{PC}^\perp \le \|b_{n,PC}\|_2^2 .$$
--
--   The noise vector controls the mass that an optimal PhaseCut solution puts outside the range of $A$. Together with (21) this bounds the distance between $V_{PC}$ and its compression $V_{PC}^{/\!/}$ in the proof of Lemma A.1, and it is used again in Lemma A.2.
--
--   **Formalization Note.** The paper cites this bound as (22) on p. 25, but the label is printed nowhere; it is the last display of p. 24. The trace is real for the positive semidefinite $V_{PC}^\perp$ and is read through its real part.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Lemma A.1, last display of p. 24 (cited as (22) on p. 25)

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder


/-- **The bound cited as (22)**, proof of Lemma A.1 (p. 24, last display). If `V_PC` minimizes (13)
for `b = |Ax₀| + b_{n,PC}`, then `Tr V^⊥_PC ≤ ‖b_{n,PC}‖₂²`. -/
theorem eq_22 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (x₀ : Fin p → ℂ) (bnPC : Fin n → ℝ)
    (VPC : Matrix (Fin n) (Fin n) ℂ) (hV : IsMin13 A (absAx A x₀ + bnPC) VPC) :
    (Vperp A VPC).trace.re ≤ vnorm bnPC ^ 2 := by sorry
end PhaseCut.Stable
