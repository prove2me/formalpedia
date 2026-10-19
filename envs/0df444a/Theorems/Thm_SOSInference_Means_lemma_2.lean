-- Prove2me | Theorems.Thm_SOSInference_Means_lemma_2
-- name    : SOSInference.Means.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:32.569312+00:00
-- url     : https://prove2.me/theorems/1635b379-c70e-4f82-9801-d8632412c4f3
-- title:
--   Lemma 2 — Poisson approximation: $\mathbb P[T_i(n,\lambda)\le t]-\mathbb P[\tau(\lambda)\le t]=O(t^{1+1/l}/n^{1/l})$
-- statement:
--   Assume A1)–A4) in dimension $l\ge1$, with densities $f_X,f_Y$ differentiable with bounded gradients. Fix $\lambda\in\mathbb R^l$, a finite $t>0$ and an index $i$. Then, as $n\to\infty$,
--   $$\mathbb P\big[T_i(n,\lambda)\le t\big]-\mathbb P\big[\tau(\lambda)\le t\big]=O\Big(\frac{t^{1+1/l}}{n^{1/l}}\Big),$$
--   that is, there is a constant $C$ (depending on $t$, $\lambda$, $i$ and the model) with $\big|\mathbb P[T_i(n,\lambda)\le t]-\mathbb P[\tau(\lambda)\le t]\big|\le C\,t^{1+1/l}/n^{1/l}$ for all $n>i$.
--
--   The number of sample points in a ball of volume of order $t/n$ is approximately Poisson with mean $\Lambda(X_i,\lambda)t$; the lemma quantifies this binomial-to-Poisson approximation for the first-arrival time.
--
--   **Formalization Note** The constant is not uniform in $t$. Only the first clause of Lemma 2 is posed; the second clause ("$=\mathbb P[\tau>t]O(1/n^l)$") is not supported by the estimate (26) its proof cites. For $l\ge2$ the regularity hypothesis is part of A4); for $l=1$, where A4) asks only for positive densities, it is added, since the $O(n^{-1/l})$ rate rests on a Taylor expansion of the density.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 41, Lemma 2 (first clause)

import Mathlib
import Definitions.Def_SOSInference_Means_Tarr
import Definitions.Def_SOSInference_Means_tauLaw

namespace SOSInference.Means

open MeasureTheory

/-- **Lemma 2** (first clause), p. 41 (Blanchet, Kang, Sample Out-of-Sample Inference Based on
Wasserstein Distance, arXiv:1605.01340v4, p. 41, Lemma 2): the Poisson approximation to the
binomial. Under A1)–A4), for fixed `λ ∈ ℝ^l`, any finite `t > 0` and every index `i`,
`P[T_i(n, λ) ≤ t] − P[τ(λ) ≤ t] = O(t^{1+1/l}/n^{1/l})` as `n → ∞`.

**Formalization Note.** The `O` is as `n → ∞` at fixed `t` ("any finite `t`"): the constant `C` may
depend on `t`, `λ`, `i` and the model, and is not uniform in `t`. The second clause of Lemma 2
(`= P[τ > t] O(1/n^l)`) is not posed: it is not supported by the (26) its proof cites. The
hypothesis `hreg` (densities differentiable with bounded gradients) is part of A4) for `l ≥ 2`;
for `l = 1` it is added, since A4) then asks only positivity and the `O(n^{−1/l})` rate comes
from a Taylor expansion of the density (p. 40). -/
theorem lemma_2 {l : ℕ} (hl : 1 ≤ l) (M : Model l) (hM : M.Standing) (hreg : M.SmoothDensities)
    (lam : E l) (t : ℝ) (ht : 0 < t) (i : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ hi : i < n,
      |(M.P {ω | Tarr M n ⟨i, hi⟩ lam ω ≤ t}).toReal - ((tauLaw M lam) (Set.Iic t)).toReal| ≤
        C * t ^ (1 + 1 / (l : ℝ)) / (n : ℝ) ^ (1 / (l : ℝ)) := by sorry

end SOSInference.Means
