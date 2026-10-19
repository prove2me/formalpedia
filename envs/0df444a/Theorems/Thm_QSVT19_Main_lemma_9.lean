-- Prove2me | Theorems.Thm_QSVT19_Main_lemma_9
-- name    : QSVT19.Main.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:31.679417+00:00
-- url     : https://prove2.me/theorems/a7a56f29-9cd8-4746-bae2-9733adba1298
-- title:
--   Lemma 9: Chebyshev polynomials via quantum signal processing
-- statement:
--   Let $d\ge1$ and let $T_d$ be the $d$-th Chebyshev polynomial of the first kind. Take $\varphi_1=(1-d)\frac\pi2$ and $\varphi_i=\frac\pi2$ for $2\le i\le d$. Then for every $x\in[-1,1]$ the top-left entry of $\prod_{j=1}^d\bigl(e^{i\varphi_j\sigma_z}R(x)\bigr)$ is $T_d(x)$:
--   $$\prod_{j=1}^d\bigl(e^{i\varphi_j\sigma_z}R(x)\bigr)=\begin{pmatrix}T_d(x)&\cdot\\ \cdot&\cdot\end{pmatrix}.$$
--
--   It gives explicit phases for the Chebyshev polynomials, which in particular satisfy the requirements of Corollary 8.
--
--   **Formalization Note** $T_d$ is Mathlib's `Polynomial.Chebyshev.T`, characterized by $T_d(\cos\theta)=\cos(d\theta)$.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 13, Lemma 9

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Lemma 9, p. 13: "Let T_d ∈ R[x] be the d-th Chebyshev polynomial of the first kind. Let
Φ ∈ R^d be such that φ_1 = (1 − d)π/2, and for all i ∈ [d] \ {1} let φ_i := π/2. Using this Φ in
equation (14) we get that P = T_d."

**Formalization Note.** "Using this Φ in (14) we get P = T_d" is: the top-left entry of
`∏_{j=1}^d e^{iφ_jσ_z}R(x)` equals `T_d(x)` for every `x ∈ [−1, 1]` (the domain of `R(x)`). The
0-based index `j = 0` is the paper's `φ_1`. `T_d` is Mathlib's `Polynomial.Chebyshev.T ℝ d`
(integer-indexed, at `d : ℕ`), which satisfies `T_d(cos θ) = cos(dθ)` as in §2. `1 ≤ d` because
`φ_1` must exist. -/
theorem lemma_9 (d : ℕ) (hd : 1 ≤ d) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspRefl (fun j : Fin d => if j.val = 0 then (1 - (d : ℝ)) * Real.pi / 2 else Real.pi / 2) x 0 0 = (((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x : ℝ) : ℂ) := by sorry

end QSVT19.Main
