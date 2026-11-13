-- Prove2me | Theorems.Thm_SaglamGV_parseval_muHat_and_log_vol
-- name    : SaglamGV.parseval_muHat_and_log_vol
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:34.841213+00:00
-- url     : https://prove2.me/theorems/c1c5cae5-1acd-43df-9341-f64ec793b7b9
-- title:
--   Parseval $\mathbb E_x\hat\mu(x)^2=1/V$ and $\lg V=nH_2(\rho)+O(\lg n)$
-- statement:
--   1. For every $n$ and every $d\ge2$, $\mathbb E_y\,\hat\mu(y)^2=1/V$.
--   2. There is an absolute constant $C$ such that for all $n\ge2$ and $1\le w\le n/2$, with $d=w+1$ and $\rho=w/n$,
--   $$
--   \big|\lg V-nH_2(\rho)\big|\le C\lg n .
--   $$
--
--   Together these give the normalization $\mathbb E\hat\mu^2=2^{-nH_2(\rho)+O(\lg n)}$ needed to apply the third-moment bound to $\hat\mu$.
--
--   Differences from the source:
--   - generalization: Parseval's identity in the regime of Appendix A → every n and every d ≥ 2; reason: Parseval's identity does not use the regime
--   - generalization: lg V = nH₂(ρ) + O(lg n) for ρ = w/n in the regime lg n ≪ w ≤ (1/2 − ε)n → one absolute constant C for all n ≥ 2 and 1 ≤ w ≤ n/2; reason: a uniform constant on a range containing the paper's specializes to it
--   - encoding: O(lg n) → |lg V − nH₂(w/n)| ≤ C·lg n for n ≥ 2; reason: the usual meaning of O(·) with an explicit constant
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), Appendix A, p.6 (display E_x µ̂(x)² = 1/V, lg V = nH₂(ρ) + O(lg n))

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SelectiveDPT_H2
import Definitions.Def_SaglamGV_Walk
import Definitions.Def_SaglamGV_Fourier

namespace SaglamGV

/-- Parseval and the size of $V$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), Appendix A, p.6: "Moreover, Parseval's identity and
Stirling's formula give E_x µ̂(x)^2 = 1/V, lg V = nH_2(ρ) + O(lg n)").

(a) For $d ≥ 2$, $E_y \hat μ(y)^2 = 1/V$. (b) There is an absolute constant $C$ with
$|\lg V − nH_2(w/n)| ≤ C \lg n$ for all $n ≥ 2$ and $1 ≤ w ≤ n/2$, where $d = w + 1$.

**Formalization Note** $H_2$ is the published `SelectiveDPT.H2` (`Real.binEntropy p / Real.log 2`, the binary entropy in bits). The $O(\lg n)$ is made uniform over $1 ≤ w ≤ n/2$, a range containing the
paper's $ρ ≤ 1/2 − ε$; $\lg$ is `Real.logb 2`. -/
theorem parseval_muHat_and_log_vol :
    (∀ n d : ℕ, 2 ≤ d → avgY (fun y => muHat n d y ^ 2) = 1 / (vol n d : ℝ)) ∧
      ∃ C : ℝ, ∀ n w : ℕ, 2 ≤ n → 1 ≤ w → 2 * w ≤ n →
        |Real.logb 2 (vol n (w + 1)) - n * SelectiveDPT.H2 ((w : ℝ) / n)| ≤ C * Real.logb 2 n := by sorry

end SaglamGV
