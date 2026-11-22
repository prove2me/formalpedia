-- Prove2me | Theorems.Thm_SchwartzDist_contDiff_of_tendsto_iteratedDeriv_nhdsNE_zero
-- name    : SchwartzDist.contDiff_of_tendsto_iteratedDeriv_nhdsNE_zero
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:47.714365+00:00
-- url     : https://prove2.me/theorems/76666c45-e799-4e29-889b-968d78ccd40a
-- title:
--   Extension by zero of a function smooth on $\mathbb R\setminus\{0\}$ whose derivatives all tend to $0$ at $0$ is smooth and flat at $0$
-- statement:
--   **Smoothness of extensions by zero of flat functions.** Let $F$ be a real normed space (e.g. $F=\mathbb C$) and let $f:\mathbb R\to F$ be a function with $f(0)=0$ that is $C^\infty$ on $\mathbb R\setminus\{0\}$, and such that every derivative tends to $0$ at the origin:
--   $$\lim_{x\to0,\ x\neq0}f^{(k)}(x)=0\qquad\text{for every }k\ge0 .$$
--   Then $f$ is $C^\infty$ on all of $\mathbb R$ and is flat at the origin:
--   $$f^{(k)}(0)=0\qquad\text{for every }k\ge0 .$$
--   In other words, the extension by zero to $\mathbb R$ of a smooth function on $\mathbb R^\times$ whose derivatives of all orders vanish at $0$ is smooth.
--
--   The paper uses this on p. 257, in the proof of Lemma 5.3.3.3(3), to show that the extension by zero of $\phi\in\mathcal S_{(-\infty,+\infty)}(\mathbf R^\times)$ is smooth at $0$, hence a Schwartz function flat at $0$. This gives the surjectivity of the restriction operator $\mathcal S_{00}(\mathbf R)\to\mathcal S_{(-\infty,+\infty)}(\mathbf R^\times)$.
--
--   **Formalization Note.** "Extension by zero" is encoded by the hypothesis $f(0)=0$. `iteratedDeriv k f x` is the $k$-th derivative of $f$ at $x$; for $x\ne0$ it is the ordinary derivative of the smooth function $f|_{\mathbb R\setminus\{0\}}$, because $\mathbb R\setminus\{0\}$ is open. The limit is taken along the punctured neighbourhood filter `𝓝[≠] 0`. `∞` denotes $C^\infty$ smoothness. The source considers complex-valued $\phi$; here any real normed target space $F$ is allowed (same proof).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 257, proof of Lemma 5.3.3.3(3) (smoothness at $0\in\mathbf R$ of the extension by zero of $\phi\in\mathcal S_I(\mathbf R^\times)$)

import Mathlib

open Topology Filter
open scoped ContDiff

set_option autoImplicit false

namespace SchwartzDist

theorem contDiff_of_tendsto_iteratedDeriv_nhdsNE_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ → F)
    (hf : ContDiffOn ℝ ∞ f {0}ᶜ) (h0 : f 0 = 0)
    (hlim : ∀ k : ℕ, Tendsto (iteratedDeriv k f) (𝓝[≠] 0) (𝓝 0)) :
    ContDiff ℝ ∞ f ∧ ∀ k : ℕ, iteratedDeriv k f 0 = 0 := by sorry

end SchwartzDist
