-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_D_1
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:14:26.941848+00:00
-- url     : https://prove2.me/theorems/b53f4ccf-19ab-4a8e-a948-8df447364d2b
-- title:
--   Lemma D.1 (used in the proof of Theorem 4.4) — High-share optimum and singleton candidates
-- statement:
--   Let $f$ be a nonnegative monotone submodular finite set function and let $c_i\ge0$. In the nontrivial branch of Appendix D, let $O$ be a nonempty feasible minimum-payment team attaining $\mathrm{OPT}=V(f,c)>0$. Write $\kappa=\kappa(O)$ and let $M$ be the best utility of the empty team and feasible singletons. Then
--   $$\kappa\ge2/3\ \Longrightarrow\ \exists i:\ g(\{i\})\ge\kappa\,\mathrm{OPT},$$
--   where the singleton is feasible. Furthermore,
--   $$M<(2/3)\mathrm{OPT}\ \Longrightarrow\ \kappa<2/3,\qquad f(O)\le3\mathrm{OPT}\le3nM.$$
--   This preserves both the high-share conclusion and the complete reward-scale bound. Empty or zero-value optima are the initialization branch, rather than hypotheses assumed of every instance.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: the analysis fixes a nonempty positive-utility optimal feasible team O → explicit nonemptiness, feasibility, attainment and positive optimum binders; reason: these are the standing assumptions immediately before Lemma D.1; the algorithm separately retains the empty team and handles M=0
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma D.1, printed p. 36 (PDF p. 38)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Benchmarks

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma D.1, printed 36 / PDF 38, in its nontrivial optimal-team branch. -/
theorem lemma_D_1 {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ)
    (hf : IsTechnology f) (hc : ∀ i, 0 ≤ c i) (O : Finset (Fin n))
    (hO : O.Nonempty) (hfeas : IsMinimumTeam f c O) (hopt : g f c O = V f c)
    (hpos : 0 < V f c) :
    ((2 / 3 : ℝ) ≤ kappa f c O →
      ∃ i : Fin n, IsMinimumTeam f c {i} ∧ kappa f c O * V f c ≤ g f c {i}) ∧
    (initialValue f c < (2 / 3 : ℝ) * V f c →
      kappa f c O < (2 / 3 : ℝ) ∧ f O ≤ 3 * V f c ∧
        3 * V f c ≤ 3 * (n : ℝ) * initialValue f c) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
