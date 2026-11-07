-- Prove2me | Theorems.Thm_RGGDetect_lemma_2
-- name    : RGGDetect.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:08.391434+00:00
-- url     : https://prove2.me/theorems/bc65c026-fc6a-46ce-83a1-2f0306b68986
-- title:
--   Lemma 2 — truncated second moment of spherical harmonics
-- statement:
--   There is a constant $C$ depending only on the total degree $2t(D)$ such that for every event $E\in\sigma(x_1,\dots,x_n)$ with $0<\mathbb P(E)\le1/2$,
--
--   $$
--   \mathbb E(D^2\mathbf 1_E)\le C\,\mathbb E(D^2)\,\mathbb P(E)\log^{\nu(D)}\Big(\frac e{\mathbb P(E)}\Big), \tag{26}
--   $$
--
--   where $\mathbb P$ is the product spherical prior of the latent points. Here $D$ is a nonzero element of $\mathcal H_{\boldsymbol\ell}$ with positive multidegree and $\nu(D)$ is (24).
--
--   This bound is used to control every rare-event contribution in the cavity argument.
--
--   **Formalization Note** $C>0$ is chosen after $t$ and before $n,d,V,\boldsymbol\ell,D,E$; $d\ge1$.
--
--   Differences from the source: none.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 2, eq. (26), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly

open MeasureTheory

namespace RGGDetect

/-- **Lemma 2** (truncated second moment of spherical harmonics; arXiv:2610.08517, held version,
sha256 e7bebd4a…, Lemma 2, p.10, eq. (26)): there is a constant `C` depending only on the total
degree `2t(D)` such that for every event `E ∈ σ(x₁, …, x_n)` with `0 < P(E) ≤ 1/2`,
`E(D² 1_E) ≤ C E(D²) P(E) log^{ν(D)}(e/P(E))`, where `P` is the product spherical prior.

**Formalization Note** `D` is a nonzero element of `H_ℓ` with `ℓ_v ≥ 1` on `V` and `‖ℓ‖₁ = 2t`
(the standing assumptions of §3, p.9); `ν(D)` is (24). The constant is chosen after `t` and before
`n, d, V, ℓ, D, E`. `d ≥ 1`. -/
theorem lemma_2 (t : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 1 ≤ d →
    ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), (∀ v ∈ V, 1 ≤ ℓ v) → ∑ v ∈ V, ℓ v = 2 * t →
    ∀ D : Config n d → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 →
    ∀ E : Set (Config n d), MeasurableSet E → 0 < (prior n d).real E →
      (prior n d).real E ≤ 1 / 2 →
      ∫ x in E, D x ^ 2 ∂(prior n d) ≤
        C * (∫ x, D x ^ 2 ∂(prior n d)) * (prior n d).real E *
          Real.log (Real.exp 1 / (prior n d).real E) ^ nuD V ℓ D := by sorry

end RGGDetect
