-- Prove2me | Theorems.Thm_SymPolyOpt_Putinar_glinear_eq_average
-- name    : SymPolyOpt.Putinar.glinear_eq_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:00.993145+00:00
-- url     : https://prove2.me/theorems/9e608b35-3c00-4751-87f4-b5c512e4ffe1
-- title:
--   §3, p. 10, after Theorem 3.2 — a G-linear map satisfies L(p) = (1/|G|) Σ_σ L^G(p^σ) = L^G((1/|G|) Σ_σ p^σ)
-- statement:
--   Let $G$ be a finite subgroup of $\mathrm{GL}_n(\mathbb R)$ acting on $\mathbb R[X]$ by $p^\sigma(x)=p(\sigma^{-1}x)$, and let $L^G:\mathbb R[X]\to\mathbb R$ be $G$-linear, i.e. linear with $L^G(f)=L^G(f^\sigma)$ for all $f$ and all $\sigma\in G$. Then for every $p\in\mathbb R[X]$,
--   $$L^G(p)=\frac1{|G|}\sum_{\sigma\in G}L^G(p^\sigma)=L^G\Big(\frac1{|G|}\sum_{\sigma\in G}p^\sigma\Big).$$
--
--   Since $\frac1{|G|}\sum_\sigma p^\sigma$ is $G$-invariant, a $G$-linear map is determined by its values on the invariant ring $\mathbb R[X]^G$; this is why the forms (3.1) need only moments indexed by a basis of $\mathbb R[X]^G$.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 10, §3, paragraph after Theorem 3.2

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

namespace SymPolyOpt.Putinar

open MvPolynomial

theorem glinear_eq_average {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (hL : IsGLinear G L) (p : MvPolynomial (Fin n) ℝ) :
    L p = (1 / (Fintype.card G : ℝ)) * ∑ σ : G, L (polyAct (σ : GL (Fin n) ℝ) p) ∧
      L p = L ((1 / (Fintype.card G : ℝ)) • ∑ σ : G, polyAct (σ : GL (Fin n) ℝ) p) := by sorry

end SymPolyOpt.Putinar
