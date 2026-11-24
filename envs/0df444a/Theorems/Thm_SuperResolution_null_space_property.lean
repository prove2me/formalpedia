-- Prove2me | Theorems.Thm_SuperResolution_null_space_property
-- name    : SuperResolution.null_space_property
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:16:50.995466+00:00
-- url     : https://prove2.me/theorems/4a269b36-d4ca-4945-adb3-4b5516aadd26
-- title:
--   Lemma 3.1 (as proved): strong null-space property
-- statement:
--   Let $f_c\ge128$, $N\ge n=2f_c+1$, $\mathrm{SRF}=N/n$, and let $T\subset\{0,\dots,N-1\}$ have $\{t/N:t\in T\}$ separated by at least $2\lambda_c$ (wrap-around). Let $F_n$ be as in (1.9), $P_T$ the restriction to $T$ and $P_{T^c}$ the restriction to its complement.
--
--   1. There is a numerical constant $\alpha>0$, independent of $N$, $f_c$ and $T$, such that every $h\in\mathbb{C}^N$ with $F_nh=0$ obeys
--   $$\|P_Th\|_1\le\rho\,\|P_{T^c}h\|_1,\qquad\rho=1-\frac{\alpha}{\mathrm{SRF}^2}.$$
--   2. (As proved.) If moreover $f_c$ is even, $\Delta\ge2.5\,\lambda_c$ and $1/N\le0.1649\,\lambda_c$, one may take $\rho=1-0.3353\,(f_c/N)^2$.
--
--   **Formalization Note** The paper states that for $\mathrm{SRF}\ge3.03$ one can take $\alpha=0.0883$, i.e. $\rho\approx1-0.3533(f_c/N)^2$. Its proof uses Lemma 2.5, which requires $\Delta\ge2.5\lambda_c$ and gives the constant $0.3353$ (the proof's $0.3533$ is a transposition). Part 2 is what the proof establishes. The paper's lower bound $\rho>0$ is omitted (the upper bound $\rho<1$ is kept, since $\alpha>0$): any $\rho$ that works can be enlarged. $N\ge2f_c+1$ is the paper's setting, in which $P_n$ is a projection.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 3, Lemma 3.1, eq. (3.1), pp. 25–26

import Mathlib
import Definitions.Def_SuperResolution_Basic

open MeasureTheory

namespace SuperResolution

theorem null_space_property :
    (∃ a : ℝ, 0 < a ∧ ∀ (N fc : ℕ), 128 ≤ fc → 2 * fc + 1 ≤ N → ∀ T : Finset (Fin N),
      ENNReal.ofReal (2 / fc) ≤ minSep (T.image (gridPt N)) →
      ∀ h : Fin N → ℂ, (∀ k : ℤ, |k| ≤ fc → partialFourier h k = 0) →
        l1norm (projT T h) ≤ (1 - a / srf N fc ^ 2) * l1norm (projT Tᶜ h)) ∧
    (∀ (N fc : ℕ), 128 ≤ fc → Even fc → 2 * fc + 1 ≤ N → (fc : ℝ) / N ≤ 0.1649 →
      ∀ T : Finset (Fin N), ENNReal.ofReal (2.5 / fc) ≤ minSep (T.image (gridPt N)) →
      ∀ h : Fin N → ℂ, (∀ k : ℤ, |k| ≤ fc → partialFourier h k = 0) →
        l1norm (projT T h) ≤ (1 - 0.3353 * ((fc : ℝ) / N) ^ 2) * l1norm (projT Tᶜ h)) := by sorry

end SuperResolution
