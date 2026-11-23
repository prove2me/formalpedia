-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_Supplement_theorem_12
-- name    : SampleDrivenOS.Structure.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:50:58.611568+00:00
-- url     : https://prove2.me/theorems/06f629d7-6ce6-4998-b8ec-9805b397f38a
-- title:
--   Theorem 12 — common limit of both sampling models
-- statement:
--   Fix any 0≤p<1 and any optimizer t* of the full infinite reduced program SDRP_p. Let β_{N,p}(t*) be the finite competitive ratio of its threshold algorithm, β_{N,p} the optimum over all adapted rank policies under independent sampling, β(p) their asymptotic value, and α(p) the separately published SDCLP value. Then
--   $$
--   \beta_{N,p}(t^*)\downarrow\beta(p)=\alpha(p).
--   $$
--   The statement includes nonincreasing finite threshold guarantees, their convergence to β(p), convergence of the finite independent optima to β(p), and the equality of that value with α(p). The optimizer premise concerns SDRP_p alone and does not assume any of these performance conclusions.
--
--   This companion theorem makes the limiting continuous guarantee applicable to each finite independent-sampling instance and identifies the two sampling-model values.
--
--   Differences from the source:
--   - encoding: β(p) is defined as the limit of β_{N,p} → β(p) is the infimum over positive N and the theorem also asserts convergence of β_{N,p} to it; reason: §2.2 states monotonicity; the limit identification remains a theorem conclusion, separate from α(p)
--   - encoding: N tends to infinity through positive integers → all sequences are indexed by N+1; reason: this reindexing changes no finite size or limit
--   - encoding: α(p) is defined as lim_{N→∞} α_{N,p} (§2.3, PDF 6) → α(p) is the published SDCLP_p optimum SampleDrivenOS.Limit.sdclpValue p; reason: the series' published convention; §4.2 (PDF 16) identifies lim α_{N,p} with the optimal value of SDCLP_p/SDRP_p, and Theorem 13 asserts α_{N,p}→sdclpValue p, so no instance changes
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 19, Theorem 12

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds

open Filter
open scoped Topology

namespace SampleDrivenOS.Structure.Supplement

theorem theorem_12 (p : ℝ) (hp : 0 ≤ p ∧ p < 1) (t : ℕ → ℝ)
    (ht : IsOptimalThresholds p t) :
    Antitone (fun N : ℕ => thresholdRatio (N + 1) p t) ∧
    Tendsto (fun N : ℕ => thresholdRatio (N + 1) p t) atTop (𝓝 (betaValue p)) ∧
    Tendsto (fun N : ℕ => betaFinite (N + 1) p) atTop (𝓝 (betaValue p)) ∧
    betaValue p = SampleDrivenOS.Limit.sdclpValue p := by sorry

end SampleDrivenOS.Structure.Supplement
