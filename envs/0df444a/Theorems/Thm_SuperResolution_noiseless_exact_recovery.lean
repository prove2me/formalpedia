-- Prove2me | Theorems.Thm_SuperResolution_noiseless_exact_recovery
-- name    : SuperResolution.noiseless_exact_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:14:47.482623+00:00
-- url     : https://prove2.me/theorems/39e5bafe-71a3-484b-b776-30369ffd24ce
-- title:
--   Theorem 1.2: exact recovery of separated spikes by total-variation minimization
-- statement:
--   Let $f_c\ge128$ be an integer, let $T\subset\mathbb{T}$ be finite, and let $x=\sum_{t\in T}a_t\delta_t$ with $a_t\in\mathbb{C}\setminus\{0\}$, so that $T$ is the support of $x$. Observe $y(k)=\int_{\mathbb{T}}e^{-i2\pi kt}x(\mathrm{d}t)$ for $|k|\le f_c$.
--
--   1. If $\Delta(T)\ge2/f_c=2\lambda_c$, then $x$ is the unique solution of
--   $$\min_{\tilde x}\|\tilde x\|_{\mathrm{TV}}\quad\text{subject to}\quad\int e^{-i2\pi kt}\tilde x(\mathrm{d}t)=y(k),\ |k|\le f_c,$$
--   over all finite complex measures $\tilde x$ on $\mathbb{T}$.
--   2. If $x$ is real-valued ($a_t\in\mathbb{R}$), the same conclusion holds under the weaker separation $\Delta(T)\ge1.87\,\lambda_c$.
--
--   The convex program knows neither the number of spikes nor their locations, yet it recovers both exactly from the $2f_c+1$ lowest Fourier coefficients.
--
--   **Formalization Note** The separation is the wrap-around distance of Definition 1.1, with $\Delta(T)=+\infty$ for a single spike. In part 2 the competitors are all finite complex measures, as in the program (1.4). The paper's proof covers only even $f_c$ explicitly, and part 2 is proved only in outline (Section 2.5); both are recorded in the mission report.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 1.2, Theorem 1.2, eqs. (1.2)–(1.6), p. 5; proof in Section 2 and Appendix A

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem noiseless_exact_recovery (fc : ℕ) (hfc : 128 ≤ fc) (T : Finset UnitAddCircle)
    (a : UnitAddCircle → ℂ) (ha : ∀ t ∈ T, a t ≠ 0) :
    (ENNReal.ofReal (2 / fc) ≤ minSep T → IsUniqueTVSolution fc (atomicMeasure T a)) ∧
    ((∀ t ∈ T, (a t).im = 0) → ENNReal.ofReal (1.87 / fc) ≤ minSep T →
      IsUniqueTVSolution fc (atomicMeasure T a)) := by sorry

end SuperResolution
