-- Prove2me | Theorems.Thm_RegevLWE_Hyperplane_expectation_chain
-- name    : RegevLWE.Hyperplane.expectation_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:52.582978+00:00
-- url     : https://prove2.me/theorems/c970f003-bb77-4d12-9e95-5a371f268b4d
-- title:
--   Proof of Lemma 3.15, p. 34:31 — E_{x∼D_{L,r}}[exp(−π(⟨w,x⟩/r)²)] ≤ det(L*) rⁿ (1 + ε) / (√2 ρ_r(L))
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice with dual $L^*$, let $\epsilon > 0$ and $r > 0$ with $r \ge \sqrt2\,\eta_\epsilon(L)$, and let $w \in \mathbb{R}^n$ be a unit vector. Write
--   $$E := \mathop{\mathrm{Exp}}_{x \sim D_{L,r}}\Bigl[\exp\bigl(-\pi(\langle w, x\rangle/r)^2\bigr)\Bigr] = \sum_{x \in L} D_{L,r}(x)\, \exp\bigl(-\pi\langle w, x\rangle^2/r^2\bigr).$$
--   Then
--
--   1. $E = \dfrac{1}{\rho_r(L)} \displaystyle\sum_{x \in L} \exp\Bigl(-\pi\,\frac{\|x\|^2 + \langle w, x\rangle^2}{r^2}\Bigr)$;
--   2. $E = \dfrac{\det(L^*)\, r^n}{\sqrt2\,\rho_r(L)} \displaystyle\sum_{y \in L^*} \exp\Bigl(-\pi r^2\Bigl(\|y\|^2 - \frac{\langle w, y\rangle^2}{2}\Bigr)\Bigr)$;
--   3. $E \le \dfrac{\det(L^*)\, r^n}{\sqrt2\,\rho_r(L)}\, \rho_{\sqrt2/r}(L^*)$;
--   4. $E \le \dfrac{\det(L^*)\, r^n}{\sqrt2\,\rho_r(L)}\, (1 + \epsilon)$.
--
--   For $w = (1, 0, \dots, 0)$ these are the four lines of the displayed chain in the proof of Lemma 3.15: the exponent in (1) is $-\pi\bigl((\sqrt2 x_1/r)^2 + (x_2/r)^2 + \dots + (x_n/r)^2\bigr)$, and the one in (2) is $-\pi\bigl((r y_1/\sqrt2)^2 + (r y_2)^2 + \dots + (r y_n)^2\bigr)$. Line (2) is Poisson summation (Lemma 2.14) for an anisotropic Gaussian, and line (4) is where the smoothing hypothesis enters.
--
--   **Formalization Note** The paper assumes "without loss of generality" that $(1, 0, \dots, 0)$ is orthogonal to the subspace $H$, i.e. it rotates coordinates; the statement is given for an arbitrary unit vector $w$, which is the coordinate-free form of that reduction. The hypothesis $\|w\| = 1$ forces $n \ge 1$. $\det(L^*)$ is written as $(\texttt{ZLattice.covolume } L)^{-1}$. $\epsilon > 0$ and $r > 0$ are the paper's standing readings (Definition 2.10 is for $\epsilon > 0$; $r$ is a Gaussian width).
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:31, proof of Lemma 3.15, displayed chain

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

namespace RegevLWE.Hyperplane

theorem expectation_chain {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (h : Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam L ε ≤ r)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    (∑' x : L, discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) =
      1 / rhoLattice r L * ∑' x : L,
        Real.exp (-Real.pi * (‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
          (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2) / r ^ 2) ∧
    (∑' x : L, discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) =
      (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) * ∑' y : RegevLWE.GaussConv.dual L,
        Real.exp (-Real.pi * r ^ 2 * (‖(y : EuclideanSpace ℝ (Fin n))‖ ^ 2 -
          (inner ℝ w (y : EuclideanSpace ℝ (Fin n))) ^ 2 / 2)) ∧
    (∑' x : L, discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
      (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) *
        rhoDual (Real.sqrt 2 / r) L ∧
    (∑' x : L, discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
      (ZLattice.covolume L)⁻¹ * r ^ n / (Real.sqrt 2 * rhoLattice r L) * (1 + ε) := by sorry

end RegevLWE.Hyperplane
