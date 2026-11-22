-- Prove2me | Theorems.Thm_PaleyWiener_paley_wiener_schwartz
-- name    : PaleyWiener.paley_wiener_schwartz
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:46.662035+00:00
-- url     : https://prove2.me/theorems/a0e5e3eb-d4ff-4bd6-b656-9c077301602c
-- title:
--   Paley–Wiener–Schwartz: $F=\int\varphi(x)e^{-ixz}dx$ with $\varphi\in C^\infty$, $\operatorname{supp}\varphi\subseteq[-A,A]$ iff $F$ entire and $(1+|z|)^N|F(z)|\le C_Ne^{A|\operatorname{Im}z|}$
-- statement:
--   **Paley–Wiener–Schwartz theorem for smooth compactly supported functions on $\mathbb R$.** Let $A\in\mathbb R$ and $F\colon\mathbb C\to\mathbb C$. The following are equivalent:
--   1. $F$ is the Fourier–Laplace transform of a smooth function supported in $[-A,A]$: there is $\varphi\in C^\infty(\mathbb R)$ (complex-valued) with $\operatorname{supp}\varphi\subseteq[-A,A]$ and
--   $$F(z)=\int_{\mathbb R}\varphi(x)\,e^{-ixz}\,dx\qquad(z\in\mathbb C);$$
--   2. $F$ is entire and of exponential type $A$ with rapid decay along horizontal lines: for every $N\in\mathbb N$ there is $C_N$ with
--   $$(1+|z|)^N\,|F(z)|\le C_N\,e^{A|\operatorname{Im}z|}\qquad(z\in\mathbb C).$$
--   (For $A<0$ both conditions just say $F=0$.)
--
--   This is the smooth counterpart of the $L^2$ Paley–Wiener theorem on a bounded interval (on the platform as `MasulloGRH.paley_wiener_compact_support`). Through $x=\log t$ it characterizes the Mellin transforms $\int_0^\infty\phi(t)t^{s}\,dt/t$ of test functions $\phi\in C_c^\infty(\mathbb R_{>0})$ supported in $[e^{-A},e^{A}]$ as the entire functions with $(1+|s|)^N|M\phi(s)|\le C_Ne^{A|\operatorname{Re}s|}$. In the source, §9.2.1 identifies Mellin transforms of functions supported in $[1/a,1]$ with a Paley–Wiener space of entire functions (Theorem 9.2.1.2(3) and its proof on p. 406, which uses the $L^2$ version of this theorem).
--
--   **Formalization Note.** $C^\infty$ is `ContDiff ℝ (⊤ : ℕ∞)`; the support is the closed support `tsupport`. The sign convention is $e^{-ixz}$ (then $|e^{-ixz}|=e^{x\operatorname{Im}z}\le e^{A|\operatorname{Im}z|}$ for $|x|\le A$); with $e^{+ixz}$ one replaces $\varphi(x)$ by $\varphi(-x)$. The integral in (1) is a Bochner integral of a continuous compactly supported function, so it always converges.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 406, proof of Theorem 9.2.1.2(3) (Paley–Wiener space $\mathrm{PW}^{2N,2}_b(\mathbf C,a)$ of entire functions; the proof further refers the reader to 'the argument in [Yos, Ch. VI, §4, Thm. 2, p. 164]')

import Mathlib

set_option autoImplicit false

namespace PaleyWiener

theorem paley_wiener_schwartz (A : ℝ) (F : ℂ → ℂ) :
    (∃ φ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ tsupport φ ⊆ Set.Icc (-A) A ∧
      ∀ z : ℂ, F z = ∫ x : ℝ, φ x * Complex.exp (-(Complex.I * z * x))) ↔
    (Differentiable ℂ F ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ z : ℂ,
      (1 + ‖z‖) ^ N * ‖F z‖ ≤ C * Real.exp (A * |z.im|)) := by sorry

end PaleyWiener
