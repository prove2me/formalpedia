-- Prove2me | Theorems.Thm_PhaseCut_Stable_eq_21
-- name    : PhaseCut.Stable.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:26.352875+00:00
-- url     : https://prove2.me/theorems/97895e9c-9b2c-4863-9ee4-87da742aa0db
-- title:
--   (21), proof of Lemma A.1, p. 24 — ‖V − V^∥‖₂² ≤ (√2 √Tr V^∥ √Tr V^⊥ + Tr V^⊥)² for V ⪰ 0
-- statement:
--   Let $A \in \mathbb{C}^{n\times p}$ and let $P = AA^\dagger$ be the orthogonal projector onto $\mathcal{R}(A)$. For a Hermitian positive semidefinite $V \in \mathbf{H}_n$ write $V^{/\!/} = PVP$ and $V^\perp = (I - P)V(I-P)$ for its restrictions to $\mathcal{R}(A)$ and $\mathcal{R}(A)^\perp$. Then, with $\|\cdot\|_2$ the Frobenius norm,
--   $$\|V - V^{/\!/}\|_2^2 \le \Big(\sqrt{2}\,\sqrt{\operatorname{Tr} V^{/\!/}}\,\sqrt{\operatorname{Tr} V^\perp} + \operatorname{Tr} V^\perp\Big)^2. \tag{21}$$
--
--   The bound says that $V$ is close to its compression onto $\mathcal{R}(A)$ as soon as the trace of its part on $\mathcal{R}(A)^\perp$ is small; in the paper it is the first step of the proof of Lemma A.1, applied to a minimizer of (13).
--
--   **Formalization Note.** The paper derives (21) for the minimizer $V_{PC}$ of (13), but uses only $V_{PC} \succeq 0$; the formal statement holds for every positive semidefinite $V$. $\operatorname{Tr} V^{/\!/}$ and $\operatorname{Tr} V^\perp$ are real and nonnegative for $V \succeq 0$ and are read through their real parts.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Lemma A.1, Eq. (21), p. 24

import Mathlib
import Definitions.Def_PhaseCut_Stable_Defs

namespace PhaseCut.Stable

open Matrix
open scoped ComplexOrder


/-- **(21)**, proof of Lemma A.1 (p. 24). For every `V ⪰ 0`, with `V^∥ = AA† V AA†` and
`V^⊥ = (I − AA†) V (I − AA†)`,
`‖V − V^∥‖₂² ≤ (√2 √(Tr V^∥) √(Tr V^⊥) + Tr V^⊥)²`. -/
theorem eq_21 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V.PosSemidef) :
    frob (V - Vpar A V) ^ 2 ≤
      (Real.sqrt 2 * Real.sqrt (Vpar A V).trace.re * Real.sqrt (Vperp A V).trace.re
        + (Vperp A V).trace.re) ^ 2 := by sorry
end PhaseCut.Stable
