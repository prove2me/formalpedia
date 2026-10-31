-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_norm_le_of_schrodinger_source
-- name    : QAlgorithms.Nannicini.norm_le_of_schrodinger_source
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-30T14:20:06.640142+00:00
-- url     : https://prove2.me/theorems/3408cf9f-4bb6-43f2-8890-fd664aba719f
-- title:
--   Norm growth for a Schrödinger equation with a source term
-- statement:
--   Let $H(s)$ be Hermitian for $s\in[0,1]$, $T\in\mathbb R$, and let $f$ satisfy $f'(s)=iT\,H(s)f(s)+h(s)$ on $[0,1]$ (derivative within $[0,1]$) with $\|h(s)\|\le M$. Then $\|f(1)\|\le\|f(0)\|+M$. (Since $\mathrm{Re}\langle f,iTHf\rangle=0$, $\frac{d}{ds}\|f\|\le\|h\|$.)
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5, §9.2 (proof of Corollary 9.24); cf. Jansen–Ruskai–Seiler, J. Math. Phys. 48 (2007) 102111, and Kato, J. Phys. Soc. Japan 5 (1950). https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- If `f′ = iT H(s) f + h(s)` on `[0, 1]` with `H(s)` Hermitian and `T` real, then the unitary
part does not change `‖f‖`, so `‖f(1)‖ ≤ ‖f(0)‖ + sup ‖h‖` (Duhamel / energy estimate). -/
theorem norm_le_of_schrodinger_source {ι : Type*} [Fintype ι] (H : ℝ → Matrix ι ι ℂ)
    (hH : ∀ s ∈ Set.Icc (0 : ℝ) 1, (H s).IsHermitian) (T : ℝ)
    (f h : ℝ → EuclideanSpace ℂ ι)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (Complex.I • (T : ℂ) • act (H s) (f s) + h s) (Set.Icc 0 1) s)
    (M : ℝ) (hM : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖h s‖ ≤ M) : ‖f 1‖ ≤ ‖f 0‖ + M := by
  sorry

end QAlgorithms.Nannicini
