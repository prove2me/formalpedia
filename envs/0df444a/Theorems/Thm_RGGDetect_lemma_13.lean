-- Prove2me | Theorems.Thm_RGGDetect_lemma_13
-- name    : RGGDetect.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:45.546749+00:00
-- url     : https://prove2.me/theorems/f912e5b3-0e76-4984-b956-e715e45cc962
-- title:
--   Lemma 13 — cap coefficients $w_\ell\le p[C(L+\ell)]^\ell/\ell!$, $(\alpha_\ell)^2\le C_Mp(dL)^\ell$
-- statement:
--   There is an absolute constant $C$ such that for $d\ge3$, $0<p\le e^{-1}$ and every integer $1\le\ell\le d$, the normalized coefficients $w_\ell=\alpha_\ell^2/N_\ell$ satisfy
--
--   $$
--   w_\ell\le\frac{p[C(L+\ell)]^\ell}{\ell!}, \tag{131}
--   $$
--
--   with $L=\log(1/p)$. Moreover, for any fixed $M$,
--
--   $$
--   (\alpha_\ell)^2=N_\ell w_\ell\le C_Mp(dL)^\ell \tag{132}
--   $$
--
--   for all $1\le\ell\le2M$.
--
--   These are the coefficient bounds for the zonal expansion (54) of the cap kernel.
--
--   **Formalization Note** $p=\mathbb P\{\langle x_1,x_2\rangle\ge\tau\}$; $\alpha_\ell$ is (129). In (132) $C_M>0$ is chosen after $M$; $\ell\le d$ is not assumed there.
--
--   Differences from the source: none.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 13, eqs. (131)–(132), p.35 (PDF p.37)

import Mathlib
import Definitions.Def_RGGDetect_harmCoef

namespace RGGDetect

/-- **Lemma 13** (cap coefficients; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 13, p.35,
eqs. (131)–(132)): there is an absolute constant `C` such that for `d ≥ 3`, `0 < p ≤ e^{-1}` and every
integer `1 ≤ ℓ ≤ d`, `w_ℓ ≤ p[C(L + ℓ)]^ℓ/ℓ!` (131), `L = log(1/p)`. Moreover, for any fixed `M`,
`(α_ℓ)² = N_ℓ w_ℓ ≤ C_M p (dL)^ℓ` for all `1 ≤ ℓ ≤ 2M` (132).

**Formalization Note** `p = capProb d τ`; `α_ℓ` is (129) and `w_ℓ = α_ℓ²/N_ℓ`. In (132) the constant
`C_M` is chosen after `M`, and `ℓ ≤ d` is not assumed (it is not in the printed statement). -/
theorem lemma_13 :
    (∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ τ : ℝ, 0 < capProb d τ →
      capProb d τ ≤ Real.exp (-1) → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ d →
        wC d τ ℓ ≤ capProb d τ * (C * (Real.log (1 / capProb d τ) + ℓ)) ^ ℓ / (ℓ.factorial : ℝ)) ∧
    (∀ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ τ : ℝ, 0 < capProb d τ →
      capProb d τ ≤ Real.exp (-1) → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * M →
        alphaC d τ ℓ ^ 2 = harmDim d ℓ * wC d τ ℓ ∧
        alphaC d τ ℓ ^ 2 ≤ C * capProb d τ * ((d : ℝ) * Real.log (1 / capProb d τ)) ^ ℓ) := by sorry

end RGGDetect
