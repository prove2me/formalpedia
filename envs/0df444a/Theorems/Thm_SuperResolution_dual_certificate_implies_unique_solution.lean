-- Prove2me | Theorems.Thm_SuperResolution_dual_certificate_implies_unique_solution
-- name    : SuperResolution.dual_certificate_implies_unique_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:11:49.458178+00:00
-- url     : https://prove2.me/theorems/d2d5ccf5-d274-43ea-88b6-cc28798e6e45
-- title:
--   Proposition A.1: a dual polynomial certifies exact recovery
-- statement:
--   Let $f_c\in\mathbb{N}$, let $T\subset\mathbb{T}$ be finite, and let $x=\sum_{t\in T}a_t\delta_t$ with $a_t\ne0$ for all $t\in T$, so that $T$ is the support of $x$. Suppose that for every $v\in\mathbb{C}^{|T|}$ with $|v_t|=1$ there is a low-frequency trigonometric polynomial $q(t)=\sum_{k=-f_c}^{f_c}c_ke^{i2\pi kt}$ with
--
--   $$q(t)=v_t\ \ (t\in T),\qquad |q(t)|<1\ \ (t\in\mathbb{T}\setminus T).$$
--
--   Then $x$ is the unique solution of $\min\|\tilde x\|_{\mathrm{TV}}$ subject to $\int e^{-i2\pi kt}\tilde x(\mathrm{d}t)=\int e^{-i2\pi kt}x(\mathrm{d}t)$ for $|k|\le f_c$, over all finite complex measures $\tilde x$ on $\mathbb{T}$.
--
--   This reduces exact recovery to the existence of an interpolating dual polynomial for every sign pattern on the support.
--
--   **Formalization Note** The support is a finite set (the paper's $v\in\mathbb{C}^{|T|}$), and sign patterns are written as functions $v$ on $\mathbb{T}$ whose values off $T$ are irrelevant.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Appendix A, Proposition A.1, eqs. (1.4), (2.1), (2.2), p. 39

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem dual_certificate_implies_unique_solution (fc : ℕ) (T : Finset UnitAddCircle)
    (a : UnitAddCircle → ℂ) (ha : ∀ t ∈ T, a t ≠ 0)
    (hcert : ∀ v : UnitAddCircle → ℂ, (∀ t ∈ T, ‖v t‖ = 1) →
      ∃ c : ℤ → ℂ, (∀ t ∈ T, trigPoly fc c t = v t) ∧ ∀ t, t ∉ T → ‖trigPoly fc c t‖ < 1) :
    IsUniqueTVSolution fc (atomicMeasure T a) := by sorry

end SuperResolution
