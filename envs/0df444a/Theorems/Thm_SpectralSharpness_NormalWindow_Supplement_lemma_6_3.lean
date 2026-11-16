-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_lemma_6_3
-- name    : SpectralSharpness.NormalWindow.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:18:22.491334+00:00
-- url     : https://prove2.me/theorems/277e1bfe-e745-4085-8b51-c8c3586aebde
-- title:
--   Lemma 6.3 — Gibbs scaling profile
-- statement:
--   Let S_d be the square-wave truncation and Φ(t)=(2/π)∫₀ᵗ sin(u)/u du, with the removable value at zero filled by 1. The convergence is through positive odd d and is uniform on every compact subset of [0,∞).
--
--   Lemma 6.3 (Gibbs scaling profile). Put Φ(t) = (2/π) ∫_0^t (sin u)/u du. Then, uniformly for t in compact
--   subsets of [0, ∞),
--   S_d(t/(d + 1)) → Φ(t) as d → ∞,
--   and Φ(π) = G = 1.1789797444 . . ., the Gibbs limit of Lemma 2.3(ii). Moreover Φ is strictly increasing
--   on [0, π] with Φ(0) = 0 and Φ(π) > 1, so for every γ ∈ (0, 1) the abscissa
--   t_γ := Φ^(−1)(γ) ∈ (0, π)
--   exists and is unique.
--
--   $$
--   S_d\!\left(\frac t{d+1}\right)\longrightarrow\Phi(t)=\frac2\pi\int_0^t\frac{\sin u}{u}\,du,\qquad \Phi(t_\gamma)=\gamma,\quad0<t_\gamma<\pi.
--   $$
--
--   This statement supplies the source’s supporting result for the associated companion theorem.
--
--   Differences from the source:
--   - encoding: odd positive integer d and d tending to infinity through odd integers → d=2m+1 with m a natural number tending to infinity; reason: this parametrizes exactly the permitted degrees, including d=1
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - encoding: uniform convergence on compact subsets of [0,∞) and the unique inverse in (0,π) → uniform convergence on each [0,R], R≥0, and the infimum-selected inverse on [0,π] with uniqueness asserted; reason: every compact subset is contained in such an interval; uniqueness identifies the selected inverse
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Lemma 6.3, p. 14

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem lemma_6_3 :
    (∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun m t => truncation (oddDegree m) (t/((oddDegree m:ℝ)+1)))
      gibbsProfile atTop (Set.Icc 0 R)) ∧
    gibbsProfile Real.pi=gibbsConstant ∧
    Tendsto (fun m => supNorm (truncation (oddDegree m))) atTop (nhds (gibbsProfile Real.pi)) ∧
    StrictMonoOn gibbsProfile (Set.Icc 0 Real.pi) ∧ gibbsProfile 0=0 ∧ 1 < gibbsProfile Real.pi ∧
    (∀ γ : ℝ, 0 < γ ∧ γ < 1 →
      (∃! t : ℝ, t ∈ Set.Ioo 0 Real.pi ∧ gibbsProfile t=γ) ∧
      gibbsInverse γ ∈ Set.Ioo 0 Real.pi ∧ gibbsProfile (gibbsInverse γ)=γ) := by sorry

end SpectralSharpness.NormalWindow.Supplement
