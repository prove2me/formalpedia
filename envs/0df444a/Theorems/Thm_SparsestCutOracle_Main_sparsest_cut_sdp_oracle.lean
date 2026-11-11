-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_sparsest_cut_sdp_oracle
-- name    : SparsestCutOracle.Main.sparsest_cut_sdp_oracle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:46:36.530993+00:00
-- url     : https://prove2.me/theorems/d61f9c05-c262-4286-961a-d4f18466c888
-- title:
--   Theorem 6 — The weighted sparsest-cut SDP oracle
-- statement:
--   Write $\Pi=\sum_i\pi(i)$ and $D_\pi=\operatorname{diag}(\pi)$. The graph has $n\ge2$ vertices and $m$ listed edges. Admissibility means $c_1/\log n\le\kappa\le c_2$, with real $\kappa$.
--
--   There are constants $c_1,c_2,b>0$, $b\le1/12$, such that for every admissible $\kappa$, every $\alpha>0$, and $0<\beta\le b$, a finite oracle program operates on the normalized positive semidefinite candidate $X$ with strictly positive weights. It succeeds with high probability with width
--
--   $$\rho=C_w\frac\alpha\Pi(\log n)^2.$$
--
--   A response is valid for SDP 2 and augments the graph by capacity at most $C_e\alpha\beta$. Otherwise it returns a cut with $\beta\Pi\le\pi(S)\le\pi(V\setminus S)$ and capacity at most $C_q(\alpha/\Pi)\sqrt{\log n/\kappa}\,\pi(S)$. The expected number of fairness-two calls is at most $C_{\mathrm{calls}} n^\kappa(\log n)^c$; every query has $\Theta(n)$ vertices and $\Theta(m)$ edges. All width, balance, size and approximation constants precede the instance and failure exponent.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: calls to FairCutFlow → a finite oracle-relative program, uniformly over every correct measurable fair-flow service, with explicit expected call count and graph-size bounds; reason: the query-only ideal service models valid subroutine outputs; measurability is the standing convention for a randomized procedure; no arbitrary function is a program instruction; raw query endpoints, capacities, counts and demands must already be well formed, so parsing performs no free repair
--   - reading: with high probability → for every natural exponent a, a measurable event of probability at least 1 − n^(−a); reason: the program and time constants may depend on a; qualitative approximation constants precede a
--   - reading: Theorem 6 does not print a failure probability → a high-probability oracle, with measurable success events; reason: p.26 explicitly says a union bound over sketches preserves the high-probability guarantee
--   - encoding: width Õ(α/Π) → width C_w(α/Π)(log n)² with C_w fixed before the instance; reason: the proof on pp.25–26 yields this explicit logarithmic power
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 18–19, Theorem 6 and Equation (6); p. 26

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Oracle

namespace SparsestCutOracle.Main

/-- Theorem 6, pp.18–19, with the high-probability reading established by p.26. -/
theorem sparsest_cut_sdp_oracle :
    ∃ c₁ c₂ b Cq Cadd Cwidth Csize : ℝ, ∃ cP : ℕ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < b ∧ b ≤ (1 / 12 : ℝ) ∧
      0 < Cq ∧ 0 < Cadd ∧ 0 < Cwidth ∧ 1 ≤ Csize ∧ 1 ≤ cP ∧
      ∀ a : ℕ, ∃ P : Procedure, ProcAdmissible P ∧ NoMatvec P ∧
        ∃ c : ℕ, ∃ Ccalls : ℝ, 0 < Ccalls ∧
        ∀ O : FairService, ValidFairService O →
        ∀ (n : ℕ) (G : Graph n) (π : Fin n → ℝ) (X : Mat n) (κ α β : ℝ),
          2 ≤ n → G.NoLoops → G.Connected → (∀ v, 0 < π v) → X.PosSemidef →
          dot (D π) X = totalWeight π →
          c₁ / Real.log n ≤ κ → κ ≤ c₂ → 0 < α → 0 < β → β ≤ b →
          let s := oracleInput G π X [κ, α, β]
          QuerySizes P O s ((n : ℝ) / Csize) (Csize * n)
            ((G.length : ℝ) / Csize) (Csize * G.length) ∧
          ExpectedCalls P O s (Ccalls * (n : ℝ) ^ κ * Real.log n ^ c) ∧
          ProcHighProbability n a P O noMatvec s
            (fun out => OracleOutcome (cP := cP) G π X α β κ Cq Cadd Cwidth out.machine) := by sorry

end SparsestCutOracle.Main
