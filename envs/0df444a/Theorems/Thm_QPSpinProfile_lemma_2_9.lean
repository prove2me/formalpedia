-- Prove2me | Theorems.Thm_QPSpinProfile_lemma_2_9
-- name    : QPSpinProfile.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:52.434193+00:00
-- url     : https://prove2.me/theorems/77475883-8c33-42c6-9fc2-075e0a4ab257
-- title:
--   Lemma 2.9: ground-state energy benchmark
-- statement:
--   There is a universal constant $c_0>0$ such that for every fixed $p\ge3$,
--   $$
--   \mathbb P\Big(\frac1{\sqrt n}\lambda_{\max}(H_{n,p})\ge c_0\frac{3^{p/2}}{p}\Big)\longrightarrow1\qquad(n\to\infty).
--   $$
--
--   The paper obtains this from Corollary D.2 of Anschuetz–Chen–Kiani–King (2025) by the rescaling $H_{n,p}=3^{p/2}\widetilde H_{n,p}$; it sets the ground-state scale against which Theorem 1.2(i) measures the gap.
--
--   Differences from the source:
--   - encoding: Pauli strings $P^a_I$ and independent standard Gaussian coefficients $g_P$ → words $w : \mathrm{Fin}\,n \to \mathrm{Fin}\,4$ with exactly $p$ non-identity letters; the disorder is a vector $g \in \mathbb R^{\mathcal P_{n,p}}$ with law $\bigotimes_P N(0,1)$; reason: bijection with the pairs $(I, a)$; same model
--   - encoding: $3^{p/2}$ → $(\sqrt3)^p$; reason: equal
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Lemma 2.9, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_QPSpinProfile_maxEnergy

namespace QPSpinProfile

open MeasureTheory Filter Topology

/-- **Lemma 2.9 (Ground-state energy benchmark)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.27, PDF p.30).
There is a universal constant `c₀ > 0` such that for every fixed `p ≥ 3`,
`P(λ_max(H_{n,p})/√n ≥ c₀ 3^{p/2}/p) → 1` as `n → ∞`.

**Formalization Note** The paper obtains this from [ACKK25, Corollary D.2] by the rescaling
`H_{n,p} = 3^{p/2} H̃_{n,p}`; `3^{p/2} = (√3)^p`. -/
theorem lemma_2_9 : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ p : ℕ, 3 ≤ p →
      Tendsto (fun n : ℕ => gaussMeasure n p
        {g | c₀ * Real.sqrt 3 ^ p / p ≤ lambdaMax n p g / Real.sqrt n}) atTop (𝓝 1) := by sorry

end QPSpinProfile
