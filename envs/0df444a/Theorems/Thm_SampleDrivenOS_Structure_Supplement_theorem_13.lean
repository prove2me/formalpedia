-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_Supplement_theorem_13
-- name    : SampleDrivenOS.Structure.Supplement.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:53:12.287972+00:00
-- url     : https://prove2.me/theorems/321c1713-9d85-4afc-ae0b-b87c166a996f
-- title:
--   Theorem 13 — two-sided finite dependent-sampling error
-- statement:
--   For every fixed real 0≤p<1, let α_{N,p} be the optimum competitive ratio under a uniform history of exactly ⌊pN⌋ items and let α(p) be the published continuous value. Put
--   $$
--   E(N,p)=\frac{(\log N)^2}{(1-p)^2\sqrt N}.
--   $$
--   The full asymptotic assertion is
--   $$
--   \alpha_{N,p}=\alpha(p)+O(E(N,p))\qquad(N\to\infty).
--   $$
--   The statement also retains explicit eventual estimates, with a starting integer N₀≥32 allowed to depend on p:
--   $$
--   \alpha(p)-9E(N,p)-\frac1{N(1-p)}\le\alpha_{N,p}\le\alpha(p)+6E(N,p)
--   \quad(N\ge N_0).
--   $$
--   For each fixed grid parameter r∈(0,1), it separately asserts the eventual estimates from Appendix B.13 whenever r=h/N:
--   $$
--   \alpha(r)-9E(N,r)\le\alpha_{N,r}\le\alpha(r)+6E(N,r).
--   $$
--   The first assertion covers irrational p and p=0. The grid statement is not a hypothesis for it. There is no claim at N=1, where log N vanishes.
--
--   This companion theorem quantifies the error between finite dependent sampling and the continuous program in both directions. The printed Lemma 20 has a log/log² discrepancy, recorded in the moderation notes; none of its estimates is made a hypothesis here.
--
--   Differences from the source:
--   - generalization: Theorem 13 displays O(E(N,p)); its proof gives grid constants 9 and 6 → the full O statement plus the proof’s eventual 9/6 grid bounds and a floor bound with rounding term 1/(N(1−p)); reason: B.13 PDF pp. 43–44 supplies 9 and 6; for r=⌊pN⌋/N the couplings in Lemmas 14 and 16 give 0≤α(p)−α(r)≤(p−r)/(1−r)≤1/(N(1−p)); E(N,r)≤E(N,p), so the full printed rate follows without restricting p
--   - encoding: as N tends to infinity → an explicit eventual threshold N₀≥32, allowed to depend on the fixed sampling parameter; reason: the proof uses sufficiently large N and Lemma 20 begins at N≥32; small sizes are not part of an asymptotic assertion
--   - encoding: α(p) is defined as lim_{N→∞} α_{N,p} (§2.3, PDF 6) → α(p) is the published SDCLP_p optimum SampleDrivenOS.Limit.sdclpValue p; reason: the series' published convention; §4.2 (PDF 16) identifies lim α_{N,p} with the optimal value of SDCLP_p/SDRP_p, and Theorem 13 asserts α_{N,p}→sdclpValue p, so no instance changes
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 19, Theorem 13; pp. 41–43, Appendix B.13

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds
import Definitions.Def_SampleDrivenOS_Structure_Supplement_FiniteLP

open Filter Asymptotics
open scoped Topology

namespace SampleDrivenOS.Structure.Supplement

theorem theorem_13 (p : ℝ) (hp : 0 ≤ p ∧ p < 1) :
    (∃ N₀ : ℕ, 32 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      SampleDrivenOS.Limit.sdclpValue p - 9 * finiteError N p -
        1 / ((N : ℝ) * (1 - p)) ≤ alphaFinite N p ∧
      alphaFinite N p ≤ SampleDrivenOS.Limit.sdclpValue p + 6 * finiteError N p) ∧
    (fun N : ℕ => alphaFinite N p - SampleDrivenOS.Limit.sdclpValue p) =O[atTop]
      (fun N : ℕ => finiteError N p) ∧
    (∀ r : ℝ, 0 < r ∧ r < 1 → ∃ N₀ : ℕ, 32 ≤ N₀ ∧ ∀ N h : ℕ,
      N₀ ≤ N → r = (h : ℝ) / (N : ℝ) →
      SampleDrivenOS.Limit.sdclpValue r - 9 * finiteError N r ≤ alphaFinite N r ∧
      alphaFinite N r ≤ SampleDrivenOS.Limit.sdclpValue r + 6 * finiteError N r) := by sorry

end SampleDrivenOS.Structure.Supplement
