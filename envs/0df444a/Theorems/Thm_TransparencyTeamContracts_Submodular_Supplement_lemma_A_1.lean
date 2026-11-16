-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_A_1
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:19:40.965604+00:00
-- url     : https://prove2.me/theorems/9be519b0-b586-4129-8ab4-aba5c069a306
-- title:
--   Lemma A.1 (used in the proof of Theorem A.2) — Full mixing reduction
-- statement:
--   Fix any finite-state model and any independent profile $x\in[0,1]^n$. Define $x_i^T=x_i$ for $i\in T$ and zero otherwise, $\widetilde f_\omega(T)=F_\omega(x^T)=\mathbb E[f_\omega(T\cap R_x)]$, and $\widetilde c_i=x_ic_i$.
--
--   1. Each auxiliary technology is monotone and $[0,1]$-valued; it preserves submodularity, supermodularity and additivity whenever the original state technology has the corresponding property.
--   2. For every posterior $\mu$ and contract $\alpha$, if $x$ is a mixed Nash equilibrium in the original instance, the full team is a pure equilibrium of the same contract in the auxiliary instance, with exactly the same principal utility.
--   3. In every state, every feasible auxiliary minimum-payment team $T$ with its actual minimum-payment contract $\beta$ is implemented in the original instance by that contract and the mixed equilibrium $x^T$, with exactly the same utility. Consequently,
--   $$\mathrm{OPT}_{\mathrm{mix}}(f_\omega,c)\ge\mathrm{OPT}(\widetilde f_\omega,\widetilde c).$$
--   Zero costs and probabilities zero or one are included. All auxiliary data are computed from the original data; no implementation or value comparison is assumed.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: independent random subsets and multilinear partial marginals → the published finite product polynomial and coordinate differences at 0 and 1; reason: finite independence gives exactly the same expectation and marginal, including boundary probabilities; no measurability or correlation restriction is added
--   - encoding: the auxiliary posterior-average reward → the auxiliary transformation of the posterior-average reward; reason: both are the same finite sum by linearity of the multilinear extension in the reward function
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma A.1, printed p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Mixed

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma A.1, printed 23–24 / PDF 25–26, all three clauses. -/
theorem lemma_A_1 {n m : ℕ} (M : Model n m) (x : Fin n → ℝ) (hx : InCube x) :
    (∀ ω, IsSuccess (auxiliaryReward (M.f ω) x) ∧
      (SubsamplingSM.Offline.IsSubmodular (M.f ω) →
        SubsamplingSM.Offline.IsSubmodular (auxiliaryReward (M.f ω) x)) ∧
      (IsSupermodular (M.f ω) → IsSupermodular (auxiliaryReward (M.f ω) x)) ∧
      (FairTeamContracts.IsAdditive (M.f ω) →
        FairTeamContracts.IsAdditive (auxiliaryReward (M.f ω) x))) ∧
    (∀ (μ : Belief m) (α : Fin n → ℝ), IsContract α →
      IsMixedNE (posteriorReward M μ) M.c α x →
      IsEquilibrium (auxiliaryReward (posteriorReward M μ) x) (auxiliaryCost M.c x) α univ ∧
      principalUtility (auxiliaryReward (posteriorReward M μ) x) α univ =
        mixedUtility (posteriorReward M μ) α x) ∧
    (∀ (ω : Fin m) (T : Finset (Fin n)),
      IsMinimumTeam (auxiliaryReward (M.f ω) x) (auxiliaryCost M.c x) T →
      let β := minimumContract (auxiliaryReward (M.f ω) x) (auxiliaryCost M.c x) T
      IsMixedNE (M.f ω) M.c β (restrictProfile x T) ∧
      mixedUtility (M.f ω) β (restrictProfile x T) =
        principalUtility (auxiliaryReward (M.f ω) x) β T) ∧
    (∀ ω, V (auxiliaryReward (M.f ω) x) (auxiliaryCost M.c x) ≤ mixedV (M.f ω) M.c) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
