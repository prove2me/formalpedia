-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_lemma_51
-- name    : SmoothedPlanted.FFK.lemma_51
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:35:04.517505+00:00
-- url     : https://prove2.me/theorems/4df13c46-bce5-49ef-9923-3cf74d30e231
-- title:
--   Lemma 51 — whp operator-norm bound ‖Q‖_op ⩽ C1(q) √(n ‖Π‖_op)
-- statement:
--   For each alphabet size $q\ge1$ there are $C_0,C_1,c>0$ and $N_0\ge2$ such that, for every $n\ge N_0$, planted set $S$, a matrix $\Pi$ with entries in $[0,1]$ and $\pi_{\min}\ge C_0\log(n)/n$, and outside distributions dominating $\Pi$,
--   $$\Pr\{\|Q\|_{\rm op}\le C_1\sqrt{n\|\Pi\|_{\rm op}}\}\ge1-n^{-c}.$$
--   No PSD inequality or symmetry of $\Pi$ is assumed for this norm bound. The scale uses the original $n$, not $n-|S|$. Constants are independent of the instance and the outside distributions.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - encoding: independent outside labels distributed as D_ij → product measure of the finite relation-valued PMFs on unordered outside pairs; reason: the joint law has full independence, not just pairwise independence; all events and moments are measurable
--   - reading: with high probability → there exist c > 0 and N0 ≥ 2, chosen before the instance, with failure probability at most n^(−c) for all n ≥ N0; reason: pins the inverse-polynomial reading; enlarging the asymptotic threshold to 2 loses no asymptotic instances
--   - generalization: Π from the FFK setting with the positive-entry lower bound → any real matrix with entries in [0,1] satisfying that positive-entry bound and distribution domination; reason: no symmetry or PSD dominance is imposed, so all source parameter cases are included
--   - reading: C0(q) and C1(q) → C0,C1 chosen after q but before every instance parameter; reason: makes the displayed dependence on q explicit
--   - encoding: natural or unspecified logarithm → Real.log, the natural logarithm; reason: another fixed base only rescales the existential C0
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Lemma 51, printed p. 33 (PDF p. 35), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Reweighted
import Definitions.Def_SmoothedPlanted_FFK_Certifiable

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem lemma_51 : ∀ q : ℕ, 1 ≤ q → ∃ C0 C1 c : ℝ, ∃ N0 : ℕ,
    0 < C0 ∧ 0 < C1 ∧ 0 < c ∧ 2 ≤ N0 ∧
    ∀ (n : ℕ) (S : Finset (Fin n)) (Pi : Matrix (Fin q) (Fin q) ℝ)
      (D : Pair (↑Sᶜ) → PMF (Relation q)),
      N0 ≤ n → (∀ a b, 0 ≤ Pi a b ∧ Pi a b ≤ 1) →
      C0 * Real.log n / n ≤ piMin Pi → Dominates D Pi →
      1 - (n : ℝ) ^ (-c) ≤
        ((outsideLaw D) {Y | spectralNorm (reweightedQ D Pi Y) ≤
          C1 * Real.sqrt ((n : ℝ) * spectralNorm Pi)}).toReal := by sorry

end SmoothedPlanted.FFK
