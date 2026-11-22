-- Prove2me | Theorems.Thm_SchwartzDist_dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta
-- name    : SchwartzDist.dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:43.752272+00:00
-- url     : https://prove2.me/theorems/af1b8f9e-e8b5-40e1-a432-2334888a7c33
-- title:
--   L. Schwartz's theorem: a tempered distribution is supported in $\{x_0\}$ iff it is a finite linear combination of derivatives of $\delta_{x_0}$
-- statement:
--   **Distributions supported at a point (L. Schwartz).** Let $E$ be a finite-dimensional real normed space (for instance $E=\mathbb R^n$, or $\mathbb C=\mathbb R^2$), let $x_0\in E$, and let $T\in\mathcal S'(E)$ be a complex tempered distribution. The support $\operatorname{supp}T$ is the smallest closed set $K\subset E$ such that $T(\varphi)=0$ for every Schwartz function $\varphi$ whose support is contained in $E\setminus K$. Derivatives of distributions are defined by transposition, $(\partial_vT)(\varphi)=-T(\partial_v\varphi)$ for $v\in E$, so that
--   $$(\partial_{v_1}\cdots\partial_{v_k}\delta_{x_0})(\varphi)=(-1)^k\,(\partial_{v_1}\cdots\partial_{v_k}\varphi)(x_0).$$
--   Then
--   $$\operatorname{supp}T\subset\{x_0\}\iff T=\sum_{j=1}^{r}c_j\,\partial_{v_{j,1}}\cdots\partial_{v_{j,k_j}}\delta_{x_0}$$
--   for some $r\ge0$, $c_j\in\mathbb C$, $k_j\ge0$ and directions $v_{j,i}\in E$. In coordinates on $E=\mathbb R^n$ the right-hand side is the classical form $T=\sum_{|\alpha|\le N}c_\alpha\,\partial^\alpha\delta_{x_0}$.
--
--   The implication from left to right is the substantial one. It is the theorem the paper recalls as Theorem 5.3.2.1, (5.3.2.1), for $E=\mathbf R$ (with $x_0=0$) and as Theorem 5.3.2.5, (5.3.2.11), for $E=\mathbf C$, where it is written with $\partial_z^k\partial_{\bar z}^{k'}\delta_0$. The proof printed for Theorem 5.3.2.5 has a gap (ERRATA I142 of the upstream formalization), but the statement (5.3.2.11) is correct. The implication from right to left is the elementary converse. The paper uses the theorem in Theorems 5.3.2.1(1) and 5.3.2.5(1) to identify the annihilator $\mathcal S_{00}^\perp$ of the space of Schwartz functions flat at the origin with a space of polynomials. This prepares the spaces $\mathcal S_{00}$ of Schwartz functions flat along coordinate hyperplanes used in §§5.3.3–5.3.4.
--
--   **Formalization Note.** The support is Mathlib's `Distribution.dsupport`: the intersection of the closed sets $s$ such that $T(\varphi)=0$ whenever `tsupport φ ⊆ sᶜ`, tested on Schwartz functions as in the definition recalled on p. 243. "Supported at $x_0$" is encoded as $\operatorname{supp}T\subset\{x_0\}$, so $T=0$ is included as the empty combination. `∂^{m}` for `m : Fin k → E` is Mathlib's iterated line derivative on `𝓢'(E, ℂ)`, which includes the transposition sign. `TemperedDistribution.delta x₀` is $\varphi\mapsto\varphi(x_0)$, and the span consists of the finite linear combinations. The source states the result at the origin for $\mathbf R$ and $\mathbf C$. Here it is stated at an arbitrary point $x_0$ of any finite-dimensional $E$, as in Hörmander's Theorem 2.3.4, which is stated there for distributions on open subsets of $\mathbb R^n$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 243, Theorem 5.3.2.1, (5.3.2.1), with proof on p. 244, and p. 246, Theorem 5.3.2.5, (5.3.2.11); classical reference: L. Hörmander, The Analysis of Linear Partial Differential Operators I, Springer-Verlag, 1983, Ch. II, Thm. 2.3.4, p. 46, together with Ch. VII, Lemma 7.1.8, p. 163 (both as cited by the paper on p. 244)

import Mathlib

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

namespace SchwartzDist

theorem dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x₀ : E) (T : 𝓢'(E, ℂ)) :
    Distribution.dsupport (⇑T) ⊆ {x₀} ↔
      T ∈ Submodule.span ℂ (Set.range fun p : (Σ k : ℕ, Fin k → E) =>
        ∂^{p.2} (TemperedDistribution.delta x₀)) := by sorry

end SchwartzDist
