-- Prove2me | Theorems.Thm_Titchmarsh_inv_riemannZeta_le_rpow_of_riemannHypothesis
-- name    : Titchmarsh.inv_riemannZeta_le_rpow_of_riemannHypothesis
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-20T23:12:58.167183+00:00
-- url     : https://prove2.me/theorems/242af0ad-5520-48fe-b514-c52cefbcd1c2
-- title:
--   Under RH, $1/\zeta(\sigma+it)=O(|t|^{\varepsilon})$ for $\sigma\ge\tfrac12+\delta$
-- statement:
--   Assume the Riemann hypothesis, in Mathlib's form: every zero $s\ne 1$ of the Riemann zeta function $\zeta$ that is not a trivial zero $-2,-4,-6,\dots$ has $\operatorname{Re}s=\tfrac12$. Then for every $\delta>0$ and every $\varepsilon>0$ there is a constant $C=C(\delta,\varepsilon)$ such that
--
--   $$
--   \left|\frac{1}{\zeta(\sigma+it)}\right|\le C\,|t|^{\varepsilon}
--   \qquad\text{whenever}\quad \tfrac12+\delta\le\sigma\le 2,\ \ |t|\ge 1 .
--   $$
--
--   In words: under RH, $1/\zeta(s)=O(|t|^{\varepsilon})$ uniformly in every closed half-strip strictly to the right of the critical line. This is equation (14.2.6) of Titchmarsh–Heath-Brown, a consequence of Littlewood's bound $\log\zeta(s)=O\big((\log t)^{2-2\sigma+\varepsilon}\big)$, uniform for $\tfrac12<\sigma_0\le\sigma\le1$ (Theorem 14.2). It is the analytic input for the conditional Mertens bound $M(x)=O(x^{1/2+\varepsilon})$ (Theorem 14.25(C)) and for many other consequences of RH.
--
--   **Formalization Note.** The bound is stated for $\operatorname{Re}s\le2$ only. For $1\le\sigma\le2$ it is classical and unconditional, and the restriction keeps the region a vertical strip. The constraint $|t|\ge1$ keeps $s$ away from the pole at $s=1$. Lean's `(riemannZeta s)⁻¹` agrees with $1/\zeta(s)$ here, since RH together with Mathlib's nonvanishing for $\operatorname{Re}s\ge1$ makes $\zeta$ zero-free on this region.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf, §14.2, Theorem 14.2 and equation (14.2.6), pp. 336–337; originally J. E. Littlewood, C. R. Acad. Sci. Paris 154 (1912), 263–266.

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Titchmarsh

theorem inv_riemannZeta_le_rpow_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ s : ℂ,
      1 / 2 + δ ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
        ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε := by sorry

end Titchmarsh
