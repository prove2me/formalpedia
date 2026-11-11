-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_approximate_iterate
-- name    : SparsestCutOracle.Main.approximate_iterate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:45:52.710354+00:00
-- url     : https://prove2.me/theorems/48d38660-cb32-4e92-ae57-d50f6ac33777
-- title:
--   Lemma 10 — Approximate coordinates suffice for the oracle
-- statement:
--   Let $\pi>0$, $\Pi=\sum_i\pi(i)$, $D_\pi=\operatorname{diag}(\pi)$, and $X=\Pi D_\pi^{-1/2}\exp(A)D_\pi^{-1/2}/\operatorname{Tr}(\exp(A))$. The graph has $n\ge2$ vertices and $m$ edges, $\alpha>0$, $0<\beta\le b\le1/12$, and $c_1/\log n\le\kappa\le c_2$.
--
--   There is a fixed $c_\gamma>0$ such that accuracy $\gamma=c_\gamma/\log n$ suffices for the current exponential Gram iterate $X$. A charged sketch program computes normalized approximate coordinates using only matrix-vector access to the exponent matrix. A separate fair-flow oracle program receives those approximate coordinates and the graph, and receives no access to the exact iterate. It returns a balanced sparse cut or a response valid on $\widetilde X$, with the usual capacity and width guarantees and
--
--   $$Z\mathbin\bullet X\ge-\alpha/10,\qquad t_Z\le C_{\mathrm{mul}}(m+n)(1+\log n)^c.$$
--
--   The feedback product must be performed by an ordinary charged program on each newly supplied vector. Both stages succeed with probability at least $1-n^{-(a+1)}$, which gives overall failure at most $n^{-a}$ for $n\ge2$. Expected fair-call counts and query graph sizes are also retained. This result justifies the approximate implementation of the oracle without replacing the exact-feedback condition by an assumed hypothesis.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - encoding: finite vertices and nonnegative real capacities → vertices Fin n and loopless edge lists with nonnegative real capacities; parallel entries are retained; reason: the edge list is the input and m is its length; summing parallel entries gives the same cut capacities
--   - encoding: calls to FairCutFlow → a finite oracle-relative program, uniformly over every correct measurable fair-flow service, with explicit expected call count and graph-size bounds; reason: the query-only ideal service models valid subroutine outputs; measurability is the standing convention for a randomized procedure; no arbitrary function is a program instruction; raw query endpoints, capacities, counts and demands must already be well formed, so parsing performs no free repair
--   - reading: the oracle and approximation succeed with high probability → each of two stages has failure probability at most n^{−(a+1)}; reason: their union has failure probability at most n^{−a} for n≥2; this union bound does not require independence
--   - generalization: the current Algorithm 1 iterate and its accurate computed sketch → any polylog-bounded symmetric exponent matrix and every normalized coordinate sketch satisfying the same multiplicative errors; reason: the proof on pp.57–59 uses only these error inequalities; actual iterates have a polylogarithmic exponent norm by p.26, so every source instance is included
--   - encoding: t_Z = Õ(m+n) → one ordinary admissible program multiplies every returned feedback matrix by every new vector within a uniform explicit polylogarithmic work bound; reason: the evaluation input contains the stored certificate and vector, not a free feedback-product oracle
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 26, Lemma 10; proof pp. 57–60

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Oracle

namespace SparsestCutOracle.Main

/-- Lemma 10, p.26. The sketch sees A only through charged matrix-vector calls;
the oracle receives only approximate coordinates. The transfer works for every accurate sketch. -/
theorem approximate_iterate :
    ∃ c₁ c₂ b Cq Cadd Cwidth Csize cγ : ℝ, ∃ cP : ℕ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < b ∧ b ≤ (1 / 12 : ℝ) ∧
      0 < Cq ∧ 0 < Cadd ∧ 0 < Cwidth ∧ 1 ≤ Csize ∧
      0 < cγ ∧ cγ ≤ (1 / 100 : ℝ) ∧ 1 ≤ cP ∧
      ∀ (pL : ℕ) (KL : ℝ), 0 < KL →
      ∀ a : ℕ,
        (∃ S : Procedure, ProcAdmissible S ∧ NoFair S ∧
          ∃ c : ℕ, ∃ C Cr : ℝ, 0 < C ∧ 0 < Cr ∧
            SketchGuarantee S (a + 1) pL KL cγ C Cr c) ∧
        (∃ P : Procedure, ProcAdmissible P ∧ NoMatvec P ∧
          ∃ M : Program, Admissible M ∧ ∃ cmul ccalls : ℕ,
          ∃ Cmul Ccalls : ℝ, 0 < Cmul ∧ 0 < Ccalls ∧
          ∀ O : FairService, ValidFairService O →
          ∀ (n r : ℕ) (G : Graph n) (π : Fin n → ℝ) (A : Mat n)
            (v : Fin n → Fin r → ℝ) (L κ α β : ℝ),
            2 ≤ n → G.NoLoops → G.Connected → (∀ i, 0 < π i) →
            A.IsSymm → 0 ≤ L → Width (fun _ => 1) L A → L ≤ KL * (1 + Real.log n) ^ pL →
            c₁ / Real.log n ≤ κ → κ ≤ c₂ → 0 < α → 0 < β → β ≤ b →
            let X := exponentialGram π A
            let Xtilde := coordsGram v
            GramAccuracy π X Xtilde (cγ / Real.log n) →
            let input := approximateOracleInput G π v κ α β
            QuerySizes P O input ((n : ℝ) / Csize) (Csize * n)
              ((G.length : ℝ) / Csize) (Csize * G.length) ∧
            ExpectedCalls P O input (Ccalls * (n : ℝ) ^ κ * Real.log n ^ ccalls) ∧
            ProcHighProbability n (a + 1) P O noMatvec input
              (fun out => ApproximateOutcome (cP := cP) G π X Xtilde α β κ Cq Cadd Cwidth
                M Cmul cmul out.machine)) := by sorry

end SparsestCutOracle.Main
