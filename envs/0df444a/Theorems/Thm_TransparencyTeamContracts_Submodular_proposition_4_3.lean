-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_proposition_4_3
-- name    : TransparencyTeamContracts.Submodular.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:40.66179+00:00
-- url     : https://prove2.me/theorems/c1835f76-4326-4e2f-9a2d-d98127d14291
-- title:
--   Proposition 4.3 — Exact additive lower bound and even-size limit
-- statement:
--   For every even integer $n\ge2$, there exists an instance with exactly $n$ agents and $n$ states, additive state technologies, and $U_P^F(D)>0$, such that
--   $$\frac{\operatorname{OPT}(D)}{U_P^F(D)}\ge\frac{U_P^N(D)}{U_P^F(D)}=R(n)=\frac{4(3n^3+n-1)}{3n^2(3n+2)}.$$
--   Moreover,
--   $$\lim_{k\to\infty}R(2(k+1))=\frac43.$$
--   These instances certify the asymptotic sharpness of the universal factor while preserving the exact ratio at every even size, including $R(2)=25/24$.
--
--   Differences from the source:
--   - encoding: finite agents and states, real probabilities and contracts, optimal utilities → Fin indices, a simplex prior, and suprema of operational contract and public-scheme payoffs; reason: finite relabeling preserves all instances; admissible payoff sets are nonempty and bounded, and suprema give the same optimal values without asserting attainment
--   - encoding: the displayed ratios and the limit as even n tends to infinity → strictly positive full-information payoff in each witness and Tendsto for n=2(k+1); reason: the source witnesses have positive denominators; 2(k+1) enumerates exactly the positive even integers, preserving the full asymptotic claim
--   - encoding: public signals on compact spaces and expected payoffs → compact Borel signal spaces, measurable posteriors and strategies, and explicit payoff integrability; reason: these are the usual meaningful-expectation conventions; finite-state measurable contract payoffs are bounded and hence integrable, so no source instance or support size is excluded
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Proposition 4.3, printed p.16 (PDF p.18), proof continues printed p.17 (PDF p.19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information
import Definitions.Def_TransparencyTeamContracts_Submodular_TightRatio

open Filter Topology

namespace TransparencyTeamContracts.Submodular

/-- Proposition 4.3, printed p.16 (PDF 18), proof continues p.17 (PDF 19).
Exactly n agents and n states; the limit runs through all positive even integers. -/
theorem proposition_4_3 :
    (∀ n : ℕ, 2 ≤ n → Even n →
      ∃ (M : Model n n) (D : Belief n),
        (∀ ω, FairTeamContracts.IsAdditive (M.f ω)) ∧
        0 < fullInformation M D ∧
        noInformation M D / fullInformation M D = tightRatio n ∧
        noInformation M D / fullInformation M D ≤
          optimalInformation M D / fullInformation M D) ∧
    Tendsto (fun k : ℕ => tightRatio (2 * (k + 1))) atTop (𝓝 (4 / 3 : ℝ)) := by sorry

end TransparencyTeamContracts.Submodular
