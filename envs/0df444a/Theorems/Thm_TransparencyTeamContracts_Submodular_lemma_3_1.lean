-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_lemma_3_1
-- name    : TransparencyTeamContracts.Submodular.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:51.544854+00:00
-- url     : https://prove2.me/theorems/84d24c9d-374c-47cf-ab42-993a2b66dcec
-- title:
--   Lemma 3.1 — All-or-Nothing Lemma (posterior-uniform form)
-- statement:
--   Fix a finite family of monotone state technologies $(f_\omega)$ and nonnegative costs $c$. Let $\beta\ge1$. If full disclosure approximates no disclosure at every prior on this same family, then it approximates the jointly optimal public information and contract scheme at every prior:
--   $$\bigl[\forall\mu\in\Delta(\Omega),\ U_P^N(\mu)\le\beta U_P^F(\mu)\bigr]\ \Longrightarrow\ \bigl[\forall D\in\Delta(\Omega),\ \operatorname{OPT}(D)\le\beta U_P^F(D)\bigr].$$
--   This is the fixed-family, posterior-uniform reduction established in the source proof. It allows a guarantee against no disclosure to control every public scheme; no submodularity is required.
--
--   Differences from the source:
--   - generalization: the premise holds for every contract setting across all technology and cost families → for each fixed technology and cost family the premise need hold only for all its priors; reason: the proof conditions only on posterior priors for that same family; the all-settings premise implies this premise for every family
--   - encoding: finite agents and states, real probabilities and contracts, optimal utilities → Fin indices, a simplex prior, and suprema of operational contract and public-scheme payoffs; reason: finite relabeling preserves all instances; admissible payoff sets are nonempty and bounded, and suprema give the same optimal values without asserting attainment
--   - encoding: public signals on compact spaces and expected payoffs → compact Borel signal spaces, measurable posteriors and strategies, and explicit payoff integrability; reason: these are the usual meaningful-expectation conventions; finite-state measurable contract payoffs are bounded and hence integrable, so no source instance or support size is excluded
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma 3.1, printed p.8 (PDF p.10), proof through printed p.9 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information

namespace TransparencyTeamContracts.Submodular

/-- Lemma 3.1 (All-or-Nothing), printed p.8 (PDF 10), proof through p.9.
The posterior-uniform fixed-family generalization established by that proof. -/
theorem lemma_3_1 {n m : ℕ} (M : Model n m) (β : ℝ) (hβ : 1 ≤ β)
    (h : ∀ μ : Belief m, noInformation M μ ≤ β * fullInformation M μ) :
    ∀ D : Belief m, optimalInformation M D ≤ β * fullInformation M D := by sorry

end TransparencyTeamContracts.Submodular
