-- Prove2me | Theorems.Thm_SymPolyOpt_Putinar_theorem_3_2
-- name    : SymPolyOpt.Putinar.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:30.563+00:00
-- url     : https://prove2.me/theorems/ab007b5c-00eb-4ff5-b517-989951d92e5d
-- title:
--   Theorem 3.2, p. 10 — a G-linear L^G is integration against a G-invariant measure on K iff every form 𝓛^G_{g_j}, 0 ≤ j ≤ m, is psd
-- statement:
--   Let $G$ be a finite subgroup of $\mathrm{GL}_n(\mathbb R)$ acting on $\mathbb R[X]=\mathbb R[X_1,\dots,X_n]$ by $p^\sigma(x)=p(\sigma^{-1}x)$. Let $g_1,\dots,g_m\in\mathbb R[X]$ be $G$-invariant, and assume that $K=\{x\in\mathbb R^n: g_j(x)\ge0,\ j=1,\dots,m\}$ satisfies Assumption 2.1. Set $g_0:=1$. Then a $G$-linear map $L^G:\mathbb R[X]\to\mathbb R$ is the integration with respect to a $G$-invariant measure on $K$, i.e. there is a finite $G$-invariant Borel measure $\mu$ with $\mu(\mathbb R^n\setminus K)=0$ and $L^G(p)=\int p\,d\mu$ for every $p$, if and only if the bilinear forms
--   $$\mathcal L^G_{g_j}:\mathbb R[X]\times\mathbb R[X]\to\mathbb R,\qquad (p,q)\mapsto L^G\Big(\frac1{|G|}\sum_{\sigma\in G}(p\cdot q)^\sigma\cdot g_j\Big)$$
--   are positive semidefinite for all $0\le j\le m$.
--
--   This is the symmetry-adapted version of Putinar's theorem. It shows that the moment relaxation of a $G$-invariant polynomial optimization problem can be posed over $G$-linear functionals, whose moments are indexed by a basis of the invariant ring, which is the source of the reduced semidefinite programs of the paper.
--
--   **Formalization Note** A form $\mathcal L^G_{g_j}$ is symmetric because $pq=qp$, so "psd" is $\mathcal L^G_{g_j}(p,p)\ge0$ for every $p\in\mathbb R[X]$, with no degree bound. The paper does not normalize: neither $L^G(1)=1$ nor a probability measure is required, and "measure on $K$" is read as a finite Borel measure carried by $K$ (this finiteness is what makes every polynomial integrable). The case $j=0$ ($g_0=1$) is included.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 10, Theorem 3.2, display (3.1)

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

namespace SymPolyOpt.Putinar

open MeasureTheory MvPolynomial

theorem theorem_3_2 {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (g : Fin m → MvPolynomial (Fin n) ℝ) (hg : ∀ j, IsGInvariant G (g j))
    (hA : Assumption21 g) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsGLinear G L) :
    (∃ μ : Measure (Fin n → ℝ), IsFiniteMeasure μ ∧ μ (feasK g)ᶜ = 0 ∧
        IsGInvariantMeasure G μ ∧ ∀ p, L p = ∫ x, eval x p ∂μ) ↔
      ∀ j : Fin (m + 1), ∀ p : MvPolynomial (Fin n) ℝ, 0 ≤ symForm G L (gExt g j) p p := by sorry

end SymPolyOpt.Putinar
