-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_D_2
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:15:06.779712+00:00
-- url     : https://prove2.me/theorems/04be04ab-1936-4e31-ab0e-c06c3abd953c
-- title:
--   Lemma D.2 (used in the proof of Theorem 4.4) — Small-agent value-oracle algorithm
-- statement:
--   There is one deterministic value-oracle program and absolute polynomial constants such that, for every $0<\zeta\le1/10$, every nonnegative monotone submodular $f$, all nonnegative costs and every $0<F_{\min}\le F_{\max}$, the program returns a feasible contract $\alpha$ and equilibrium team $T$, with total share at most one. Its utility simultaneously satisfies
--   $$U_P(\alpha,T)\ge(\gamma_\star-\zeta)(1-k)f(P)$$
--   for every $P$ and $k\in[0,1]$ with $F_{\min}\le f(P)\le F_{\max}$, $W(P)^2\le kf(P)$, and $w_i\le\eta(\zeta)\sqrt{f(P)}$ for every agent. Neither $P$ nor $k$ is supplied to the algorithm. The explicit witness is $\eta(\zeta)=\zeta^6/(32\cdot400000^3)>0$.
--
--   Arithmetic and query counts are bounded uniformly by a polynomial in $n,1/\zeta,1+\log(F_{\max}/F_{\min})$. A second query bound uses the actual finite reward-scale guesses, weight mesh and at most $\lceil112/[3(\zeta/20)^2]\rceil+2$ refill rounds, plus the cubic prefix budget. Rewards may exceed one and have positive baseline.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: deterministic value-oracle algorithms and arithmetic/query counts → a uniform finite rational-literal RAM program with an explicit query instruction, halted transcript and uniform numerical cost bounds; reason: the machine charges actual operations and queries without an optimization primitive; field-only programs implement numerical approximations internally, while D.3 uses the source exact-real convention
--   - encoding: there exists eta=Theta(zeta^6) and the Appendix D finite-loop implementation → the explicit eta constructed in the proof and a query bound formed from the supplied grids and round cap; reason: the constructed witness proves the same existence claim and fixes all accuracy dependence rather than leaving an uninterpreted poly function
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma D.2, printed p. 36 (PDF p. 38)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma D.2, printed 36 / PDF 38; the program sees no comparison team or k. -/
theorem lemma_D_2 :
    ∃ (p : OracleProgram) (C d : ℕ), FieldAdmissible p ∧ 0 < C ∧
      ∀ (ζ : ℝ), 0 < ζ → ζ ≤ (1 / 10 : ℝ) → 0 < eta ζ ∧
      ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
        IsTechnology f → (∀ i, 0 ≤ c i) →
      ∀ (Fmin Fmax : ℝ), 0 < Fmin → Fmin ≤ Fmax →
        Computes p f (machineInput c ζ Fmin Fmax 0 ∅ ∅ (fun _ => 0))
          (smallBudget C d n ζ Fmin Fmax)
          (min (smallBudget C d n ζ Fmin Fmax) (C * smallQueryBudget n ζ Fmin Fmax))
          (fun α T => Supported f c α T ∧ IsEquilibrium f c α T ∧ (∑ i, α i) ≤ 1 ∧
            ∀ (P : Finset (Fin n)) (k : ℝ), 0 ≤ k → k ≤ 1 →
              Fmin ≤ f P → f P ≤ Fmax → W c P ^ 2 ≤ k * f P →
              (∀ i, weight c i ≤ eta ζ * Real.sqrt (f P)) →
              (gamma - ζ) * (1 - k) * f P ≤ principalUtility f α T) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
