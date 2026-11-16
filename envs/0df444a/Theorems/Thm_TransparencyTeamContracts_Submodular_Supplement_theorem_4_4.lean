-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_theorem_4_4
-- name    : TransparencyTeamContracts.Submodular.Supplement.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:18:14.11324+00:00
-- url     : https://prove2.me/theorems/64014e8d-fb2d-41bf-bec2-47bffd865870
-- title:
--   Theorem 4.4 (companion theorem; not used in the proof of the goal) — Deterministic contract and full-disclosure algorithms
-- statement:
--   Let $\varpi\in(0,1)$ be the unique root of $\varpi e^\varpi=1$ and put $\gamma_\star=1-\varpi$. One uniform deterministic value-oracle program, with absolute constants $C,d$, has both guarantees for every $\epsilon>0$.
--
--   1. For every stateless monotone submodular $f:2^{[n]}\to[0,1]$ and nonnegative costs, it computes a feasible contract and a pure equilibrium team with total share at most one and
--   $$U_P\ge\frac{\mathrm{OPT}(f,c)}{\gamma_\star^{-1}+\epsilon}.$$
--   2. For every finite-state instance with submodular state technologies and arbitrary prior $D$, fully revealing the state and running the same program with accuracy $3\epsilon/4$ computes a state-dependent contract/equilibrium table with expected utility at least
--   $$\frac{\mathrm{OPT}(D)}{4/(3\gamma_\star)+\epsilon}.$$
--   The table is realized by an operational public scheme with exactly revealed-state posteriors and the computed contracts; principal-favorable selection can only improve the returned teams' expected utility.
--
--   Both arithmetic and value-query counts are at most $C(n+1)^{C(1+\lceil1/\epsilon\rceil)^d}$, with the corresponding $3\epsilon/4$ substitution per realized state. Queries also satisfy the explicit finite enumeration/grid/refill budget from Appendix D. The constants are exact omega-defined reals, not decimal approximations; the count is polynomial for each fixed accuracy and does not assert polynomial dependence on reciprocal accuracy outside the exponent.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: deterministic value-oracle algorithms and arithmetic/query counts → a uniform finite rational-literal RAM program with an explicit query instruction, halted transcript and uniform numerical cost bounds; reason: the machine charges actual operations and queries without an optimization primitive; field-only programs implement numerical approximations internally, while D.3 uses the source exact-real convention
--   - encoding: n^{poly(1/epsilon)} operations and queries per realized state, with the explicit Appendix D construction → uniform natural constants C,d, the bound C(n+1)^{C(1+ceil(1/epsilon))^d}, and the counted enumeration/grid/refill query budget; reason: this spells out one uniform polynomial exponent, handles n=0 and n=1, and preserves both charged resources and every positive real accuracy
--   - encoding: full revelation followed by the known-state algorithm at accuracy 3epsilon/4 → the same program at that accuracy, a state-dependent output table, and a diagonal joint-law PublicScheme with those contracts; reason: the finite state signal is compact Borel; its posterior is a point mass and favorable selection weakly improves each computed equilibrium
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Theorem 4.4, printed p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Theorem 4.4, printed 17 / PDF 19, both parts with the same uniform program.
The second part runs that program at accuracy 3ε/4 in each realized state. -/
theorem theorem_4_4 :
    ∃ (p : OracleProgram) (C d : ℕ), FieldAdmissible p ∧ 0 < C ∧
    (0 < omega ∧ omega < 1 ∧ omega * Real.exp omega = 1 ∧
      ∀ w : ℝ, 0 < w → w < 1 → w * Real.exp w = 1 → w = omega) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
      IsSuccess f → SubsamplingSM.Offline.IsSubmodular f → (∀ i, 0 ≤ c i) →
      Computes p f (machineInput c ε 0 0 0 ∅ ∅ (fun _ => 0))
        (mainBudget C d n ε) (min (mainBudget C d n ε) (C * mainQueryBudget n ε))
        (fun α S => Supported f c α S ∧ IsEquilibrium f c α S ∧ (∑ i, α i) ≤ 1 ∧
          V f c / (gamma⁻¹ + ε) ≤ principalUtility f α S)) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ (n m : ℕ) (M : Model n m) (D : Belief m),
      (∀ ω, SubsamplingSM.Offline.IsSubmodular (M.f ω)) →
      ∃ (α : Fin m → Fin n → ℝ) (S : Fin m → Finset (Fin n)),
        (∀ ω, Computes p (M.f ω) (machineInput M.c (3 * ε / 4) 0 0 0 ∅ ∅ (fun _ => 0))
          (mainBudget C d n (3 * ε / 4))
          (min (mainBudget C d n (3 * ε / 4)) (C * mainQueryBudget n (3 * ε / 4)))
          (fun β T => β = α ω ∧ T = S ω ∧ Supported (M.f ω) M.c β T ∧
            IsEquilibrium (M.f ω) M.c β T ∧ (∑ i, β i) ≤ 1 ∧
            V (M.f ω) M.c / (gamma⁻¹ + 3 * ε / 4) ≤ principalUtility (M.f ω) β T)) ∧
        optimalInformation M D / (4 / (3 * gamma) + ε) ≤
          (∑ ω, (D : Fin m → ℝ) ω * principalUtility (M.f ω) (α ω) (S ω)) ∧
        ∃ A : PublicScheme M D (Fin m), A.contract = α ∧
          A.joint {p | p.1 ≠ p.2} = 0 ∧
          (∀ s ω, (A.posterior s : Fin m → ℝ) ω = if ω = s then 1 else 0) ∧
          (∑ ω, (D : Fin m → ℝ) ω * principalUtility (M.f ω) (α ω) (S ω)) ≤ A.value) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
