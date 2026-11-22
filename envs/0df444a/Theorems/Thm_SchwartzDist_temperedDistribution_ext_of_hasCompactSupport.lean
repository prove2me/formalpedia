-- Prove2me | Theorems.Thm_SchwartzDist_temperedDistribution_ext_of_hasCompactSupport
-- name    : SchwartzDist.temperedDistribution_ext_of_hasCompactSupport
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:42.254107+00:00
-- url     : https://prove2.me/theorems/5b5f4746-bb74-4591-9c9a-795bd8ec9690
-- title:
--   Tempered distributions are determined by their values on compactly supported test functions ($\mathcal S'\hookrightarrow\mathcal D'$)
-- statement:
--   **Tempered distributions are distributions.** Let $E$ be a finite-dimensional real normed space (for instance $E=\mathbb R^n$) and let $F$ be a complex normed space. Let $T_1,T_2\in\mathcal S'(E,F)$ be tempered distributions, i.e. continuous $\mathbb C$-linear maps $\mathcal S(E,\mathbb C)\to F$. If
--   $$T_1(\varphi)=T_2(\varphi)\qquad\text{for every }\varphi\in\mathcal S(E,\mathbb C)\text{ with compact support},$$
--   then $T_1=T_2$.
--
--   Equivalently, restricting a tempered distribution to the compactly supported test functions $C_c^\infty(E)\subset\mathcal S(E)$ is injective. This is the classical injection $\mathcal S'(\mathbb R^n)\hookrightarrow\mathcal D'(\mathbb R^n)$, the transpose of the dense inclusion $\mathcal D(\mathbb R^n)\to\mathcal S(\mathbb R^n)$. The paper uses it on p. 244, in the proof of Theorem 5.3.2.1, to view a tempered distribution supported at $0$ as a distribution supported at $0$, and to obtain a linear bijection between the two spaces of such distributions.
--
--   **Formalization Note.** `𝓢'(E, F)` is Mathlib's `TemperedDistribution E F`, the continuous $\mathbb C$-linear maps $\mathcal S(E,\mathbb C)\to F$; its topology plays no role here. The paper treats scalar distributions ($F=\mathbb C$, $E=\mathbf R$ or $\mathbf R^m$); here the target $F$ is an arbitrary complex normed space, which contains the scalar case.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 244, proof of Theorem 5.3.2.1 (the injective operator $\mathcal S(\mathbf R)'_\beta\to\mathcal D(\mathbf R)'_\beta$); classical reference: L. Hörmander, The Analysis of Linear Partial Differential Operators I, Springer-Verlag, 1983, Ch. VII, Lemma 7.1.8, p. 163 (as cited by the paper)

import Mathlib

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace SchwartzDist

theorem temperedDistribution_ext_of_hasCompactSupport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T₁ T₂ : 𝓢'(E, F))
    (h : ∀ φ : 𝓢(E, ℂ), HasCompactSupport (φ : E → ℂ) → T₁ φ = T₂ φ) :
    T₁ = T₂ := by sorry

end SchwartzDist
