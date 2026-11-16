-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_theorem_A_2
-- name    : TransparencyTeamContracts.Submodular.Supplement.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:20:24.434384+00:00
-- url     : https://prove2.me/theorems/a68910a0-17a4-497d-9f14-c60df526702b
-- title:
--   Theorem A.2 (companion theorem; not used in the proof of the goal) — Tight transparency bound under mixed equilibria
-- statement:
--   For every finite-state monotone submodular team-contract instance, nonnegative costs and arbitrary prior, with principal-favorable independent mixed Nash equilibria under both benchmarks,
--   $$U_{P,\mathrm{mix}}^F(D)\ge\frac34\mathrm{OPT}_{\mathrm{mix}}(D).$$
--   The four-thirds loss is tight even for additive technologies: for every $1\le\beta<4/3$ there exists a finite additive instance with positive full mixed value and $\mathrm{OPT}_{\mathrm{mix}}(D)>\beta U_{P,\mathrm{mix}}^F(D)$.
--
--   The statement also asserts the equality used in the source's tightness argument: for every stateless additive success technology and nonnegative costs, $\mathrm{OPT}_{\mathrm{mix}}(f,c)=\mathrm{OPT}(f,c)$. This is a conclusion to prove, not a hypothesis. The joint mixed optimum retains all compact Borel public schemes rather than only finite posterior support.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: mixed equilibria under both full revelation and the joint optimum → independent unit-cube profiles, finite product-law rewards and operational mixed PublicSchemes; reason: these are exactly the independent mixed profiles in Appendix A, including 0 and 1, with the same meaningful-expectation conventions as the published pure model
--   - encoding: the source proof asserts equality of stateless pure and mixed optima for additive rewards and obtains tightness from Proposition 4.3 → that equality is an explicit concluding conjunct, alongside universal 3/4 utility and quantified positive-payoff sharpness; reason: the proof obligation is retained instead of assuming the equality; the two headline clauses are not weakened or split
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Theorem A.2, printed p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_Mixed

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Theorem A.2, printed 24 / PDF 26, proof through printed 25 / PDF 27.
Both sides allow independent mixed NE; additive equality is asserted, never assumed. -/
theorem theorem_A_2 :
    (∀ (n m : ℕ) (M : Model n m) (D : Belief m),
      (∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) →
      (3 / 4 : ℝ) * mixedOptimal M D ≤ mixedFull M D) ∧
    (∀ β : ℝ, 1 ≤ β → β < (4 / 3 : ℝ) →
      ∃ (n m : ℕ) (M : Model n m) (D : Belief m),
        (∀ ω, FairTeamContracts.IsAdditive (M.f ω)) ∧
        0 < mixedFull M D ∧ β * mixedFull M D < mixedOptimal M D) ∧
    (∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
      IsSuccess f → FairTeamContracts.IsAdditive f → (∀ i, 0 ≤ c i) → mixedV f c = V f c) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
