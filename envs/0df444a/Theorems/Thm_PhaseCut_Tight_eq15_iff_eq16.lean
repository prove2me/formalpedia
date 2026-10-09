-- Prove2me | Theorems.Thm_PhaseCut_Tight_eq15_iff_eq16
-- name    : PhaseCut.Tight.eq15_iff_eq16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:07.979959+00:00
-- url     : https://prove2.me/theorems/625e3432-b775-4225-8af6-06624895837a
-- title:
--   Proof of Proposition 4.2, pp. 12–13 — (15) Tr(MU) = 0, U ⪰ 0 is equivalent to (16) U = Φ(X) for some X ⪰ 0
-- statement:
--   Let $A\in\mathbb C^{n\times p}$ be injective, let $b\in\mathbb R^n$ have $b_i\neq 0$ for every $i$, and assume problem (1), $|Ax|=b$, has a solution $x\in\mathbb C^p$. Let $M=\operatorname{diag}(b)(\mathbf I-AA^\dagger)\operatorname{diag}(b)$ and $\Phi(X)=\operatorname{diag}(b)^{-1}AXA^*\operatorname{diag}(b)^{-1}$. Then for every $U\in\mathbb C^{n\times n}$,
--
--   $$\bigl(\operatorname{Tr}(MU)=0\ \text{ and }\ U\succeq 0\bigr)\iff U=\Phi(X)\ \text{ for some } X\succeq 0,\ X\in\mathbb C^{p\times p}.$$
--
--   This is the first step of the proof of Proposition 4.2: it identifies the cone cut out by the PhaseCutMod constraint $\operatorname{Tr}(MU)=0$ with the image of the positive semidefinite cone under $\Phi$, before the diagonal constraints are matched.
--
--   **Formalization Note** The hypotheses are those of Proposition 4.2, including the solvability of (1), which the page assumes for the proposition. $U\succeq 0$ and $X\succeq 0$ are Mathlib's `Matrix.PosSemidef` (Hermitian included). Injectivity makes $(A^*A)^{-1}A^*$ the pseudoinverse and $b_i\neq 0$ makes $\operatorname{diag}(b)^{-1}$ the true inverse.
-- source:
--   Waldspurger, d'Aspremont & Mallat, arXiv:1206.0102v3, proof of Proposition 4.2, eqs. (15)–(16), pp. 12–13 (cited p. 12)

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

namespace PhaseCut.Tight

open Matrix
open scoped ComplexOrder

/-- Proof of Proposition 4.2, p. 12: under the hypotheses of Proposition 4.2,
`Tr(MU) = 0, U ⪰ 0` (15) holds iff `U = Φ(X)` for some `X ⪰ 0` (16). -/
theorem eq15_iff_eq16 {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) (hsol : IsSolvable A b) :
    ∀ U : Matrix (Fin n) (Fin n) ℂ,
      ((Mmat A b * U).trace = 0 ∧ U.PosSemidef) ↔
        ∃ X : Matrix (Fin p) (Fin p) ℂ, X.PosSemidef ∧ U = Phi A b X := by sorry

end PhaseCut.Tight
