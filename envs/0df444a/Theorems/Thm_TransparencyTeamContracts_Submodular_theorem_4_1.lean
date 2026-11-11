-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_theorem_4_1
-- name    : TransparencyTeamContracts.Submodular.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:49.904664+00:00
-- url     : https://prove2.me/theorems/cfef99c2-97e1-4a87-9a78-3bfa0c6f4a14
-- title:
--   Theorem 4.1 — Tight four-thirds loss of full transparency
-- statement:
--   For every finite multi-agent contract instance with a finite nonempty state space, arbitrary prior $D$, nonnegative state-independent costs, and monotone submodular state technologies $f_\omega:2^{[n]}\to[0,1]$, full revelation satisfies
--   $$U_P^F(D)\ge\frac34\operatorname{OPT}(D).$$
--   Here $\operatorname{OPT}$ optimizes the public information and signal-dependent contract jointly with principal-favorable pure Nash equilibrium selection. No zero-baseline or positive-cost restriction is imposed.
--   The factor is sharp even for additive technologies: for every $1\le\beta<4/3$, there exists a finite additive instance with
--   $$U_P^F(D)>0,\qquad\operatorname{OPT}(D)>\beta U_P^F(D).$$
--   The two clauses form one goal. The multiplied universal inequality also covers zero optimal payoff and does not require division by the full-information value.
--
--   Differences from the source:
--   - encoding: finite agents and states, real probabilities and contracts, optimal utilities → Fin indices, a simplex prior, and suprema of operational contract and public-scheme payoffs; reason: finite relabeling preserves all instances; admissible payoff sets are nonempty and bounded, and suprema give the same optimal values without asserting attainment
--   - encoding: monotone submodularity with marginals tested for every agent → monotone IsSuccess plus the published diminishing-returns predicate for agents outside the larger set; reason: the omitted membership cases follow from monotonicity, so the function class is identical
--   - encoding: full revelation is a 4/3 approximation and that factor is tight even for additive rewards → a multiplied 3/4 utility bound conjoined with a positive-payoff additive counterexample to each beta in [1,4/3); reason: multiplication preserves the approximation guarantee at zero payoff; the quantified sharpness is precisely impossibility of any better approximation factor
--   - encoding: public signals on compact spaces and expected payoffs → compact Borel signal spaces, measurable posteriors and strategies, and explicit payoff integrability; reason: these are the usual meaningful-expectation conventions; finite-state measurable contract payoffs are bounded and hence integrable, so no source instance or support size is excluded
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Theorem 4.1, printed p.9 (PDF p.11), proof printed pp.15–17 (PDF pp.17–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Information

namespace TransparencyTeamContracts.Submodular

/-- Theorem 4.1, printed p.9 (PDF 11). Both the universal guarantee and the
additive sharpness clause are part of this single goal. -/
theorem theorem_4_1 :
    (∀ (n m : ℕ) (M : Model n m) (D : Belief m),
      (∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) →
        (3 / 4 : ℝ) * optimalInformation M D ≤ fullInformation M D) ∧
    (∀ β : ℝ, 1 ≤ β → β < (4 / 3 : ℝ) →
      ∃ (n m : ℕ) (M : Model n m) (D : Belief m),
        (∀ ω, FairTeamContracts.IsAdditive (M.f ω)) ∧
        0 < fullInformation M D ∧ β * fullInformation M D < optimalInformation M D) := by sorry

end TransparencyTeamContracts.Submodular
