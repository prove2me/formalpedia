-- Prove2me | Theorems.Thm_SphereGRF_Holder_lemma_4_2
-- name    : SphereGRF.Holder.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:35:55.125609+00:00
-- url     : https://prove2.me/theorems/136eeb9a-ffed-4e5c-9424-f73f3f86b2c3
-- title:
--   Lemma 4.2 — Hölder bound for the covariance kernel
-- statement:
--   Let $(A_\ell)_{\ell\ge0}$ be a nonnegative angular power spectrum and let $0\le\beta\le2$. If $\sum_{\ell\ge0}A_\ell\ell^{1+\beta}<\infty$, then the associated distance kernel $k$ has a constant $C_\beta$ such that
--
--   $$
--   |k(0)-k(r)|\le C_\beta r^\beta\qquad(0\le r\le\pi).
--   $$
--
--   This gives the kernel regularity used to bound Gaussian field increments. **Formalization Note** The statement includes $\beta=0$, as in Lemma 4.2, although Assumption 4.1 itself states $\beta>0$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, Lemma 4.2, p. 16

import Mathlib
import Definitions.Def_SphereGRF_Holder_Setting

open MeasureTheory ProbabilityTheory Polynomial
noncomputable section

namespace SphereGRF.Holder

theorem lemma_4_2 (A : ℕ → ℝ) (β : ℝ)
    (hA0 : ∀ ℓ, 0 ≤ A ℓ) (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA : Summable (fun ℓ : ℕ => A ℓ * (ℓ : ℝ) ^ (1 + β))) :
    ∃ C : ℝ, ∀ r : ℝ, r ∈ Set.Icc 0 Real.pi →
      |kernel A 0 - kernel A r| ≤ C * r ^ β := by sorry

end SphereGRF.Holder
