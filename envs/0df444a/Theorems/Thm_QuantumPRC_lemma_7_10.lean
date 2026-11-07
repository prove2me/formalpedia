-- Prove2me | Theorems.Thm_QuantumPRC_lemma_7_10
-- name    : QuantumPRC.lemma_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:13.276636+00:00
-- url     : https://prove2.me/theorems/1c35e943-045f-462b-ab0c-cbeb4693f7d6
-- title:
--   Lemma 7.10 — $\mathrm{SD}(\mathcal D,\mathcal D')\le2^{n-r-1}$
-- statement:
--   Let $n,r,m\in\mathbb N$. Let $\mathcal D$ be the law of $h(z)=\pi(z\|0^r)\|f(z)$ for a uniformly random function $f:\{0,1\}^n\to\{0,1\}^m$ and an independent uniformly random permutation $\pi$ of $\{0,1\}^{n+r}$, and let $\mathcal D'$ be the law of $h(z)=\pi'(z\|0^{r+m})$ for a uniformly random permutation $\pi'$ of $\{0,1\}^{n+r+m}$. Then
--
--   $$
--   \mathrm{SD}(\mathcal D,\mathcal D')=\frac12\sum_{h}\big|\Pr_{\mathcal D}[h]-\Pr_{\mathcal D'}[h]\big|\le 2^{\,n-r-1},
--   $$
--
--   the sum running over all functions $h:\{0,1\}^n\to\{0,1\}^{n+r+m}$.
--
--   This is hybrid step (175) of the pseudorandomness proof: it replaces the permutation-plus-function encoding by a single random permutation.
--
--   Differences from the source: none.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Lemma 7.10, Eq. (169), p.49 (proof pp.51–53)

import Mathlib
import Definitions.Def_QuantumPRC_pfIso

namespace QuantumPRC

/-- **Lemma 7.10** (statistical distance of the two injective-function laws). Hsieh, Yamada,
arXiv:2609.38986 (sha256 6901b59d…), Lemma 7.10, p.49: "Let `n, r, m ∈ ℕ`. Define `D` and `D′` to be the
following distributions over injective functions `{0,1}^n → {0,1}^{n+r+m}`. • `D`: Choose a uniformly
random function `f : {0,1}^n → {0,1}^m` and a uniformly random permutation `π : {0,1}^{n+r} → {0,1}^{n+r}`.
Define […] `h(z) := π(z∥0^r)∥f(z)`. Output `h`. • `D′`: Choose a uniformly random permutation
`π′ : {0,1}^{n+r+m} → {0,1}^{n+r+m}`. Define […] `h(z) := π′(z∥0^{r+m})`. Output `h`. Then, we have
`SD(D, D′) ≤ 2^{n−r−1}`."

**Formalization Note.** `SD(D, D′) = ½ Σ_h |D(h) − D′(h)|`, summed over all functions
`h : {0,1}^n → {0,1}^{n+r+m}` (both laws vanish off the injective ones). `2^{n−r−1}` is an integer power
of `2` (`zpow`), which may be `< 1`. -/
theorem lemma_7_10 (n r m : ℕ) :
    (1 / 2 : ℝ) * ∑ h : Bits n → Bits (n + r + m), |lawD n r m h - lawD' n r m h| ≤
      (2 : ℝ) ^ ((n : ℤ) - r - 1) := by sorry

end QuantumPRC
