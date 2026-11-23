-- Prove2me | Theorems.Thm_RestrictedAP_Counting_theorem_5_9_counting_interface
-- name    : RestrictedAP.Counting.theorem_5_9_counting_interface
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:57.676417+00:00
-- url     : https://prove2.me/theorems/bff242b1-55cc-4989-acf0-5957f3bf30ff
-- title:
--   Invariance interface for means and truncated triple correlations
-- statement:
--   For every error $\varepsilon>0$ there is an influence threshold $\tau=\tau(m,s,D,C,\varepsilon)>0$ such that the discrete and Gaussian multilinear polynomials have means within $\varepsilon$, each Gaussian first-moment truncation error is at most $\sqrt{\operatorname{truncatedError}(g)}+\varepsilon$, and their truncated triple correlations differ by at most
--   $$\varepsilon+12\Big(\sqrt{\operatorname{truncatedError}(g)}+\sum_{i=0}^2\mathbb E_G|M'_i-M_i|\Big).$$
--   The formulation also records the automatic Gaussian polynomial integrability. It applies verbatim at $n=0$ and $q'=0$. The constant $12$ is an explicit admissible choice for the unspecified $O(1)$ in the paper's smooth-extension estimate.
-- source:
--   Bhangale–Khot–Liu–Minzer, arXiv:2608.17365 (paper #1020), Theorem 5.9 p.30; Claims 5.23 and 5.24 pp.44–47 (mean and first-moment truncation transfer); Claim 5.26 pp.48–49 (smooth extension of $(a,b,c)\mapsto abc$ and truncated product transfer). The coefficient 12 merely instantiates the paper's $O(1)$ constant.

import Mathlib
import Definitions.Def_RestrictedAP_Counting_GaussianInterface

namespace RestrictedAP.Counting

open MeasureTheory ComplexOrder

/-- The part of Mossel's invariance principle (Theorem 5.9) used in Claims 5.23, 5.24
and 5.26: transfer of the mean, the first moment of the truncation discrepancy, and the
truncated triple product. The coefficient `12` is a convenient bound for the universal
constants arising from the smooth extension of `(a,b,c) ↦ abc`. -/
theorem theorem_5_9_counting_interface (m : ℕ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (D : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] [Nonempty Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → AtomsAtLeast μ s →
      ∀ (n q' : ℕ) (coeff : (Fin n → Fin (q' + 1)) → ℂ)
        (φ : Fin (q' + 1) → Sig → ℂ) (g : (Fin n → Sig) → ℂ)
        (A : Matrix (Fin 3 × Fin (n * q' + 1)) (Fin 3 × Fin (n * q' + 1)) ℂ),
        Fintype.card Sig = q' + 1 →
        (∀ a, φ 0 a = 1) →
        (∀ j k, ∑ a, (ν a : ℂ) * star (φ j a) * φ k a = if j = k then 1 else 0) →
        (∀ α, D < (Finset.univ.filter (fun i => α i ≠ 0)).card → coeff α = 0) →
        (∀ x, g x = multiEval coeff (fun k => φ k.2.succ (x k.1))) →
        l2Norm (tensorPow ν n) g ≤ C →
        (∀ i, influence ν i g ≤ τ) →
        (∀ (i j : Fin 3) (k l : Fin n × Fin q'),
          (A * A.conjTranspose) (i, baseCoord k) (j, baseCoord l) =
            if k.1 = l.1 then
              ∑ t, (μ t : ℂ) * φ k.2.succ (coord3 i t) * star (φ l.2.succ (coord3 j t))
            else 0) →
        (∀ i : Fin 3, Integrable (fun G => gaussianPoly coeff G i) (gaussianLaw A)) ∧
        (∀ i : Fin 3,
          ‖expectC (tensorPow ν n) g - ∫ G, gaussianPoly coeff G i ∂gaussianLaw A‖ ≤ ε) ∧
        (∀ i : Fin 3, gaussianTruncError coeff A i ≤ Real.sqrt (truncatedError ν g) + ε) ∧
        |tripleTrunc μ g - gaussianTruncTriple coeff A| ≤
          ε + 12 * (Real.sqrt (truncatedError ν g) + ∑ i : Fin 3, gaussianTruncError coeff A i) := by sorry
