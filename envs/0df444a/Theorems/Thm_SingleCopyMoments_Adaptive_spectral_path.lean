-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_spectral_path
-- name    : SingleCopyMoments.Adaptive.spectral_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:48:33.7064+00:00
-- url     : https://prove2.me/theorems/2899f7f8-5484-4360-bfdf-a251714ebc4a
-- title:
--   Lemma 31 — Moment-matching spectral path
-- statement:
--   Fix integers $r\ge2$ and $r\le t\le2r-2$. For $0\le\theta\le\pi/r$ put $\lambda_j(\theta)=(1+\cos(2\pi j/r+\theta))/r$, $0\le j<r$, and write $p_k(\lambda)=\sum_j\lambda_j^k$. These are probability vectors and their moments of orders $1,\ldots,r-1$ are constant along the whole path. The exact endpoint gap is
--
--   $$p_t(\lambda(0))-p_t(\lambda(\pi/r))=\Delta_t=2^{2-t}r^{1-t}\binom{2t}{t-r}>0.$$
--
--   For every point of the interval,
--
--   $$0\le\lambda_j\le2/r,\qquad\sum_j|\lambda'_j|\le1,\qquad\frac{|p'_\ell|}{\ell}\le(2/r)^{\ell-1}\quad(\ell\ge1).$$
--
--   This gives both exact low-order matching and separation at the target order. Derivatives are of the explicit smooth trigonometric functions on the real line, including at the interval endpoints.
--
--   Differences from the source:
--   - encoding: spectral coordinates and the closed path interval → Fin r coordinates, integer powers for the exact gap, and real derivatives of the explicit path; reason: all r coordinates and every matching order are retained, including zero endpoint weights
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 31, (7.2)–(7.4), printed p. 32 (PDF p. 34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Ensemble

namespace SingleCopyMoments.Adaptive

/-- Lemma 31, printed pp.32–33 (PDF pp.34–35). -/
theorem spectral_path (r t : ℕ) (hr : 2 ≤ r) (hrt : r ≤ t) (htr : t ≤ 2*r-2) :
    (∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / r),
      (∀ j, spectralWeight r θ j ∈ Set.Icc 0 (2/(r : ℝ))) ∧
      (∑ j, spectralWeight r θ j) = 1 ∧
      (∑ j, |deriv (fun u => spectralWeight r u j) θ|) ≤ 1 ∧
      ∀ ℓ : ℕ, 1 ≤ ℓ → |deriv (spectralMoment r ℓ) θ| / (ℓ : ℝ) ≤
        (2/(r : ℝ))^(ℓ-1)) ∧
    (∀ k : ℕ, 1 ≤ k → k < r → ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / r),
      spectralMoment r k θ = spectralMoment r k 0) ∧
    spectralMoment r t 0 - spectralMoment r t (Real.pi/r) = spectralGap r t ∧
    0 < spectralGap r t := by sorry

end SingleCopyMoments.Adaptive
