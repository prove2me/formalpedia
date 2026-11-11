-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_gram_approximation
-- name    : SparsestCutOracle.Main.gram_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:44:43.726191+00:00
-- url     : https://prove2.me/theorems/cc028480-42e1-4b88-a187-962e1b3fdae3
-- title:
--   Lemma 8 — Multiplicative Gram approximation
-- statement:
--   Write $\Pi=\sum_i\pi(i)$ and $D_\pi=\operatorname{diag}(\pi)$. Matrix and vector norms in this statement are the spectral and Euclidean norms, respectively.
--
--   Let $n\ge2$ and let $A$ be symmetric, $\pi>0$, $\Gamma=D_\pi^{-1/2}$, and $X=\Pi\Gamma\exp(A)\Gamma/\operatorname{Tr}(\exp(A))$. A known $L\ge\|A\|_2$ and $0<\gamma<1/2$ satisfy fixed polylogarithmic bounds on $L$ and $\gamma^{-1}$. Given charged matrix-vector access to $A$ at cost $t_A$ per call, one finite program computes vectors $\widetilde v_i\in\mathbb R^r$ in at most $C(t_A+n)(1+\log n)^c$ work on every tape, with $r\le C_r\gamma^{-2}\log n$ and exact normalization $\sum_i\pi(i)\|\widetilde v_i\|^2=\Pi$. With high probability, simultaneously for all $i,j$,
--
--   $$\left|\|\widetilde v_i\|^2-\|v_i\|^2\right|\le\gamma\|\widetilde v_i\|^2,\qquad
--   \left|\|\widetilde v_i-\widetilde v_j\|^2-\|v_i-v_j\|^2\right|\le\gamma\|\widetilde v_i-\widetilde v_j\|^2.$$
--
--   Here $v_i$ is any Gram representation of $X$. Exact matrix exponential appears only in the mathematical specification; it is not an instruction.
--
--   Differences from the source:
--   - reading: a randomized algorithm, with no machine specified → one finite admissible charged real-RAM program with square roots and independent standard Gaussian and fair-coin tapes; reason: the base machine is the published ClusterDecomp machine; the only new scalar instructions are square root and Gaussian sampling
--   - reading: with high probability → for every natural exponent a, a measurable event of probability at least 1 − n^(−a); reason: the program and time constants may depend on a; qualitative approximation constants precede a
--   - encoding: L and γ⁻¹ are log^{O(1)} n → fixed natural exponents and positive prefactors precede the program and instance; reason: this quantifies both hidden constants uniformly; 1+log n only changes finite-size constants
--   - reading: we can compute in Õ(t_A+n) time → an all-tape work bound for a matrix-vector-oracle program, charged t_A per call; reason: the stronger runtime reading preserves the paper’s time clause; a zero sketch may use a normalized fallback on null tapes
--   - encoding: the logarithmic dimension and complexity bounds → n ≥ 2; reason: the asymptotic logarithmic bounds are stated on their nondegenerate domain; at n=1 the literal log n factor is zero and cannot bound a normalized positive-weight sketch dimension
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 25–26, Lemma 8; proof pp. 55–57

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_MMW

namespace SparsestCutOracle.Main

/-- Lemma 8, pp.25–26. The product Au is the only oracle, charged tA per invocation.
Fixed polylog exponents and prefactors precede every instance. -/
theorem gram_approximation :
    ∀ (pL pγ : ℕ) (KL Kγ : ℝ), 0 < KL → 0 < Kγ →
    ∀ a : ℕ, ∃ P : Procedure, ProcAdmissible P ∧ NoFair P ∧
      ∃ c : ℕ, ∃ C Cr : ℝ, 0 < C ∧ 0 < Cr ∧
      ∀ (n : ℕ) (π : Fin n → ℝ) (A : Mat n) (L γ : ℝ) (tA : ℕ),
        2 ≤ n → (∀ v, 0 < π v) → A.IsSymm → 0 ≤ L →
        Width (fun _ => 1) L A → L ≤ KL * (1 + Real.log n) ^ pL →
        0 < γ → γ < (1 / 2 : ℝ) → γ⁻¹ ≤ Kγ * (1 + Real.log n) ^ pγ → 1 ≤ tA →
        let s := gramInput π L γ
        let V : MatvecContext := ⟨n, A, tA⟩
        (∀ O : FairService, ∀ ω : Tape, ProcHalts P O V s ω ∧
          let out := procFinal P O V s ω
          ((out.machine.base.work : ℕ) : ℝ) ≤ C * ((tA : ℝ) + n) * (1 + Real.log n) ^ c ∧
          (vectorDimension out.machine : ℝ) ≤ Cr * γ⁻¹ ^ 2 * Real.log n ∧
          dot (D π) (vectorGram n out.machine) = totalWeight π) ∧
        ∀ O : FairService, ProcHighProbability n a P O V s
          (fun out => GramAccuracy π (exponentialGram π A) (vectorGram n out.machine) γ) := by sorry

end SparsestCutOracle.Main
