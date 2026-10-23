-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_lemma_1
-- name    : UniversalBarrier.NSC.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:48.188889+00:00
-- url     : https://prove2.me/theorems/bae86988-0737-4ca7-aba3-4fecfe5f84e2
-- title:
--   Lemma 1, p. 4 — the first three directional derivatives of φ are moment polynomials of the polar marginal
-- statement:
--   Let $n\ge1$, let $K\subseteq\mathbb R^n$ be a proper convex domain with universal barrier $\varphi(x)=\log\mathrm{Vol}_n(K^\circ(x))$, let $x\in\operatorname{int}(K)$ and $h\in\mathbb R^n$, $h\neq0$. Let $p=p(K^\circ(x),h;\cdot)$ be the marginal density of the polar body $K^\circ(x)$ along $h$. Then
--   $$D\varphi(x)[h]=(n+1)\mu_1(p),$$
--   $$D^2\varphi(x)[h,h]=(n+1)(n+2)\mu_2^2(p)+(n+1)\mu_1^2(p),$$
--   $$D^3\varphi(x)[h,h,h]=(n+1)(n+2)(n+3)\mu_3^3(p)+6(n+1)(n+2)\mu_2^2(p)\mu_1(p)+2(n+1)\mu_1^3(p).$$
--
--   These formulas, from Nesterov and Nemirovski [10, p. 52] with sign errors corrected, turn the self-concordance inequalities for $\varphi$ into moment inequalities for $p$.
--
--   **Formalization Note.** $D^i\varphi(x)[h,\dots,h]$ is the $i$-th Fréchet derivative evaluated on $(h,\dots,h)$. The marginal is normalized by its own integral, so it is the density of $y^{\mathsf T}h$ for $y$ uniform on $K^\circ(x)$ for every $h\neq0$. The case $h=0$ (all derivatives $0$, marginal a Dirac mass) is excluded.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 4, Lemma 1

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

open scoped RealInnerProductSpace
open MeasureTheory

namespace UniversalBarrier.NSC

theorem lemma_1 {n : ℕ} (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsProperConvexDomain K) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (h : EuclideanSpace ℝ (Fin n)) (hh : h ≠ 0) :
    fderiv ℝ (universalBarrier K) x h = ((n : ℝ) + 1) * mu1 (marginalDensity (polarAt K x) h) ∧
    iteratedFDeriv ℝ 2 (universalBarrier K) x (fun _ => h) =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * mu2sq (marginalDensity (polarAt K x) h)
        + ((n : ℝ) + 1) * mu1 (marginalDensity (polarAt K x) h) ^ 2 ∧
    iteratedFDeriv ℝ 3 (universalBarrier K) x (fun _ => h) =
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * mu3cube (marginalDensity (polarAt K x) h)
        + 6 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * mu2sq (marginalDensity (polarAt K x) h)
            * mu1 (marginalDensity (polarAt K x) h)
        + 2 * ((n : ℝ) + 1) * mu1 (marginalDensity (polarAt K x) h) ^ 3 := by sorry

end UniversalBarrier.NSC
