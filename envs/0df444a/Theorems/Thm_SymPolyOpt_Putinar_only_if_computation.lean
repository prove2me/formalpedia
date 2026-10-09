-- Prove2me | Theorems.Thm_SymPolyOpt_Putinar_only_if_computation
-- name    : SymPolyOpt.Putinar.only_if_computation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:33.733322+00:00
-- url     : https://prove2.me/theorems/33b8dc2e-7762-485a-8f4a-40de0ca5a72c
-- title:
--   Theorem 3.2 proof (only if), p. 11 — for a G-invariant measure μ on K, ∫ (1/|G|) Σ_σ (f²)^σ g_j dμ = ∫ f² g_j dμ ≥ 0
-- statement:
--   Let $G$ be a finite subgroup of $\mathrm{GL}_n(\mathbb R)$, let $g_1,\dots,g_m\in\mathbb R[X]$ be $G$-invariant, put $g_0:=1$, and assume $K=\{x: g_j(x)\ge0,\ j=1,\dots,m\}$ is compact. Let $\mu$ be a finite Borel measure on $\mathbb R^n$ with $\mu(\mathbb R^n\setminus K)=0$ that is $G$-invariant ($\mu^\sigma=\mu$ for all $\sigma\in G$). Then for every $j\in\{0,\dots,m\}$ and every $f\in\mathbb R[X]$,
--   $$\int\frac1{|G|}\sum_{\sigma\in G}(f^2)^\sigma\,g_j\,d\mu=\int f^2g_j\,d\mu\qquad\text{and}\qquad\int f^2g_j\,d\mu\ge0.$$
--
--   This is the "only if" half of Theorem 3.2: the moment functional $L_\mu(f)=\int f\,d\mu$ of an invariant measure on $K$ makes every symmetrized localizing form $\mathcal L^G_{g_j}$ positive semidefinite.
--
--   **Formalization Note** $\mu$ is finite and carried by the compact set $K$, so all the integrands (polynomials) are integrable.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 11, proof of Theorem 3.2, Only if part (display)

import Mathlib
import Definitions.Def_SymPolyOpt_Putinar_Setting

namespace SymPolyOpt.Putinar

open MeasureTheory MvPolynomial

theorem only_if_computation {n m : ℕ} (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (g : Fin m → MvPolynomial (Fin n) ℝ) (hg : ∀ j, IsGInvariant G (g j))
    (hK : IsCompact (feasK g)) (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    (hμK : μ (feasK g)ᶜ = 0) (hμG : IsGInvariantMeasure G μ)
    (j : Fin (m + 1)) (f : MvPolynomial (Fin n) ℝ) :
    ∫ x, eval x ((1 / (Fintype.card G : ℝ)) •
          ∑ σ : G, polyAct (σ : GL (Fin n) ℝ) (f * f) * gExt g j) ∂μ =
        ∫ x, eval x (f * f * gExt g j) ∂μ ∧
      0 ≤ ∫ x, eval x (f * f * gExt g j) ∂μ := by sorry

end SymPolyOpt.Putinar
