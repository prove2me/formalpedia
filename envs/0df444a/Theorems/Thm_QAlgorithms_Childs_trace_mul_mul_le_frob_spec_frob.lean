-- Prove2me | Theorems.Thm_QAlgorithms_Childs_trace_mul_mul_le_frob_spec_frob
-- name    : QAlgorithms.Childs.trace_mul_mul_le_frob_spec_frob
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:32:02.344875+00:00
-- url     : https://prove2.me/theorems/f0669d59-4311-4a08-a5ee-112eabf2527b
-- title:
--   Trace inequality |tr(XYZ)| ≤ ‖X‖_F ‖Y‖ ‖Z‖_F
-- statement:
--   Let $m,n\ge 0$ be integers and let $X\in\mathbb C^{m\times n}$, $Y\in\mathbb C^{n\times n}$ and $Z\in\mathbb C^{n\times m}$ be complex matrices. Write $\|A\|_F$ for the Frobenius norm, $\|A\|_F^2=\sum_{a,b}|A_{ab}|^2$, and $\|Y\|$ for the spectral (operator) norm of $Y$, i.e. its largest singular value. Then
--
--   $$
--   |\operatorname{tr}(XYZ)| \le \|X\|_F\,\|Y\|\,\|Z\|_F .
--   $$
--
--   In the generalized adversary method this inequality bounds both the final value of the weight function for Boolean functions and how much one query can change it.
--
--   **Formalization Note** The index sets are $\{0,\dots,m-1\}$ and $\{0,\dots,n-1\}$; the Frobenius norm is `frobNorm` and the spectral norm is `specNorm` (Mathlib's $\ell^2$ operator norm on matrices). When $m=0$ or $n=0$ both sides are $0$.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 118, Proposition 23.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Proposition 23.2 (PDF p. 118): for any `X ∈ ℂ^{m×n}`, `Y ∈ ℂ^{n×n}`,
`Z ∈ ℂ^{n×m}`, `|tr(XYZ)| ≤ ‖X‖_F ‖Y‖ ‖Z‖_F`, where `‖·‖_F` is the Frobenius norm
(`‖X‖_F² = ∑_{a,b} |X_ab|²`, p. 118) and `‖Y‖` the spectral (operator) norm (§1.3). -/
theorem trace_mul_mul_le_frob_spec_frob {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin n) (Fin m) ℂ) :
    ‖(X * Y * Z).trace‖ ≤ frobNorm X * specNorm Y * frobNorm Z := by
  sorry

end QAlgorithms.Childs
