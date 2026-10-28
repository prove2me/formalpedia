-- Prove2me | Theorems.Thm_PhaseCut_Stable_lemma_A_2
-- name    : PhaseCut.Stable.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:27.68988+00:00
-- url     : https://prove2.me/theorems/7419c05b-d958-4f4e-890d-489c7e73b50b
-- title:
--   Lemma A.2, p. 25 — ‖b_{n,PL}‖₂ ≤ 2‖b_{n,PC}‖₂
-- statement:
--   Let $A \in \mathbb{C}^{n\times p}$, $x_0 \in \mathbb{C}^p$ and $b_{n,PC} \in \mathbb{R}^n$. Let $V_{PC}$ be a minimizer of problem (13) for $b = |Ax_0| + b_{n,PC}$, let $V_{PC}^{/\!/} = AA^\dagger V_{PC} AA^\dagger$ be its restriction to $\mathcal{R}(A)$, and define $b_{n,PL} \in \mathbb{R}^n$ by
--   $$b_{n,PL,i} = \sqrt{(V_{PC}^{/\!/})_{ii}} - |Ax_0|_i, \qquad i = 1,\dots,n.$$
--   Then
--   $$\|b_{n,PL}\|_2 \le 2\,\|b_{n,PC}\|_2 .$$
--
--   $b_{n,PL}$ is the noise for which $V_{PC}^{/\!/}$ is an exact solution of Weak PhaseLift; the lemma says it is at most twice the PhaseCut noise, which is how the noise level is transported from PhaseCut to Weak PhaseLift in the proof of Theorem 4.7.
--
--   **Formalization Note.** The paper's last norm "$\|b_{n,PC}\|$" is the Euclidean norm. Of the assumptions of Theorem 4.7 ("under the assumptions and notations of Theorem 4.7") only the minimality of $V_{PC}$ is used and kept; stability of Weak PhaseLift, $A \ne 0$, $C > 0$ and the smallness of $b_{n,PC}$ are not needed. The diagonal entry $(V_{PC}^{/\!/})_{ii}$ is real and nonnegative and is read through its real part.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, Lemma A.2, p. 25

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder


/-- **Lemma A.2** (p. 25). If `V_PC` minimizes (13) for `b = |Ax₀| + b_{n,PC}`, and
`b_{n,PL,i} = √(V^∥_{PC,ii}) − |Ax₀|ᵢ`, then `‖b_{n,PL}‖₂ ≤ 2 ‖b_{n,PC}‖₂`. -/
theorem lemma_A_2 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (x₀ : Fin p → ℂ) (bnPC : Fin n → ℝ)
    (VPC : Matrix (Fin n) (Fin n) ℂ) (hV : IsMin13 A (absAx A x₀ + bnPC) VPC) :
    vnorm (fun i => Real.sqrt (Vpar A VPC i i).re - absAx A x₀ i) ≤ 2 * vnorm bnPC := by sorry
end PhaseCut.Stable
