-- Prove2me | Theorems.Thm_WassVarReg_Boundary_boundaryGap_le
-- name    : WassVarReg.Boundary.boundaryGap_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:53.010316+00:00
-- url     : https://prove2.me/theorems/06d785e3-9313-4930-97c3-e49758cbe5a2
-- title:
--   p. ec11, before Lemma EC.11 — E_{P_n}[(ρ − d(z, D))₊] ≤ ρ E_{P_n}[1{d(z, D) < ρ}]
-- statement:
--   Let $(\mathcal Z, d)$ be a metric space, $D \subseteq \mathcal Z$, $\rho \ge 0$, and let $P_n = \frac1n\sum_{i=1}^n \delta_{z_i}$ be the empirical law of $n \ge 1$ points $z_1, \dots, z_n \in \mathcal Z$. Write $d(z, D) = \inf_{\tilde z \in D} d(z, \tilde z)$ with $d(z, \varnothing) = +\infty$. Then
--   $$\mathbb E_{P_n}\bigl[(\rho - d(z, D))_+\bigr] \le \rho\,\mathbb E_{P_n}\bigl[\mathbf 1\{d(z, D) < \rho\}\bigr].$$
--
--   This elementary comparison reduces the boundary term of Theorem 1(III) to the empirical mass of a $\rho$-neighbourhood of $D$, which Lemma EC.11 controls.
--
--   **Formalization Note** Empirical means are written as $\frac1n\sum_{i}$ over `Fin n`. The hypotheses $n \ge 1$ and $\rho \ge 0$ are the paper's sample-size and radius conventions; the pointwise comparison itself also holds at $n = 0$ and $\rho < 0$.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), p. ec11, display before Lemma EC.11

import Mathlib
import Definitions.Def_WassVarReg_Boundary_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WassVarReg.Boundary

/-- The inequality before Lemma EC.11, p. ec11:
`E_{P_n}[(ρ - d(z, D))₊] ≤ ρ E_{P_n}[1{d(z, D) < ρ}]`. -/
theorem boundaryGap_le {Z : Type*} [MetricSpace Z]
    (n : ℕ) (hn : 0 < n) (ω : Fin n → Z) (ρ : ℝ) (hρ : 0 ≤ ρ) (D : Set Z) :
    (1 / (n : ℝ)) * ∑ i : Fin n, WassVarReg.PInf.boundaryGap ρ D (ω i) ≤
      ρ * ((1 / (n : ℝ)) * ∑ i : Fin n, nearIndicator ρ D (ω i)) := by sorry

end WassVarReg.Boundary
