-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_D_5
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_D_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:17:11.141336+00:00
-- url     : https://prove2.me/theorems/ad087b40-d967-423b-9d96-b0962304bc2a
-- title:
--   Lemma D.5 (used in the proof of Theorem 4.4) — Large-agent deletion with a fixed residual budget
-- statement:
--   Let $f$ be nonnegative, monotone and submodular and $c_i\ge0$. Let $H,T$ be disjoint, with positive costs on $H$. Fixed shares in $[0,1]$ support agents of $T$ in $H\cup T$, and sum to $1-B_0$ for $B_0\in[0,1]$. Set $V_0=B_0 f(H\cup T)$ and
--   $$\psi_H(v)=\max\{v-W(H)\sqrt v,0\}.$$
--   A deterministic polynomial-time deletion program returns $S$ with $T\subseteq S\subseteq H\cup T$, retaining the original shares on $T$, and a feasible equilibrium contract of total share at most one whose utility is at least $\psi_H(V_0)$. Both $B_0$ and $V_0$ refer to the original team and are fixed during the call. The query bound is quadratic and the arithmetic bound polynomial, uniformly in all data.
--
--   For every $H$, $\psi_H$ is nondecreasing on $[0,\infty)$ and satisfies $|\psi_H(v)-\psi_H(w)|\le|v-w|$ for nonnegative $v,w$. No positivity of costs on $T$ is required.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: deterministic value-oracle algorithms and arithmetic/query counts → a uniform finite rational-literal RAM program with an explicit query instruction, halted transcript and uniform numerical cost bounds; reason: the machine charges actual operations and queries without an optimization primitive; field-only programs implement numerical approximations internally, while D.3 uses the source exact-real convention
--   - encoding: a retained subset of H united with T and the nondecreasing, 1-Lipschitz utility function → T subset S subset H union T with unchanged T shares, plus MonotoneOn and the absolute-difference inequality; reason: disjointness makes the set descriptions equivalent; the named residual data are computed once from the input, and the analytic properties include the boundary v=0
--   - generalization: the analytic properties of psi_H are stated for the nonnegative costs of the contract setting → the separate monotonicity and Lipschitz conjunct allows every real cost vector; reason: Real.sqrt is nonnegative for every real input (and zero at negative inputs), so W is nonnegative; the same analytic claim applies and specializes to every source cost vector
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma D.5, printed p. 44 (PDF p. 46)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma D.5, printed 44 / PDF 46. B0 and V0 refer to the original union. -/
theorem lemma_D_5 :
    (∃ (p : OracleProgram) (C d : ℕ), FieldAdmissible p ∧ 0 < C ∧
      ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
        IsTechnology f → (∀ i, 0 ≤ c i) →
      ∀ (H T : Finset (Fin n)) (α : Fin n → ℝ) (B₀ : ℝ),
        Disjoint H T → (∀ i ∈ H, 0 < c i) →
        (∀ i ∈ T, 0 ≤ α i ∧ α i ≤ 1 ∧ c i ≤ α i * teamMarginal f (H ∪ T) i) →
        0 ≤ B₀ → B₀ ≤ 1 → (∑ i ∈ T, α i) = 1 - B₀ →
        Computes p f (machineInput c 0 0 0 B₀ H T α)
          (C * (n + 1) ^ d) (C * (n + 1) ^ 2)
          (fun β S => T ⊆ S ∧ S ⊆ H ∪ T ∧ (∀ i ∈ T, β i = α i) ∧
            Supported f c β S ∧ IsEquilibrium f c β S ∧ (∑ i, β i) ≤ 1 ∧
            psi c H (B₀ * f (H ∪ T)) ≤ principalUtility f β S)) ∧
    (∀ (n : ℕ) (c : Fin n → ℝ) (H : Finset (Fin n)),
      MonotoneOn (psi c H) (Set.Ici 0) ∧
      ∀ v ∈ Set.Ici (0 : ℝ), ∀ w ∈ Set.Ici (0 : ℝ), |psi c H v - psi c H w| ≤ |v - w|) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
