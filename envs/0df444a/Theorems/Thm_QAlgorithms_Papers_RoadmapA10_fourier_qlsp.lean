-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA10_fourier_qlsp
-- name    : QAlgorithms.Papers.RoadmapA10.fourier_qlsp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:32:40.761782+00:00
-- url     : https://prove2.me/theorems/e17a8e62-fe3a-45bc-ab2c-75f6bd7384e2
-- title:
--   CKS Theorem 3: the Fourier linear-systems algorithm
-- statement:
--   Let \(N\ge1\), let \(A\in\mathbb C^{N\times N}\) be Hermitian and invertible with \(\|A\|_{\mathrm{op}}=1\), and let \(\kappa\ge1\) be a supplied upper bound on its condition number. Let \(b\ne0\), and write \(|b\rangle=b/\|b\|\) and \(|x\rangle=A^{-1}b/\|A^{-1}b\|\). The coherent preparation procedure \(P_B\) prepares \(|b\rangle\) in polynomial time in \(\log N\) on the \(\lceil\log_2 N\rceil\)-qubit state register; its inverse is available. Put \(L=\max\{1,\log(\kappa/\varepsilon)\}\), with \(0<\varepsilon<1\).
--
--   There are absolute positive constants and fixed asymptotic thresholds, chosen before all public parameters and hidden inputs, with the following two conclusions.
--
--   1. A single oracle-independent Fourier reduction for the public parameters solves the problem for every such \(A,b,P_B\) and every compatible coherent SELECT simulator. Sparsity is not needed for this conclusion. SELECT implements the signed evolutions used by the Fourier sum, uniformly on superpositions and with reverse access. Its maximum evolution time, required operator error, number of calls, and number of preparation calls satisfy
--   \[
--   |t|\le C_t\kappa L,\qquad
--   \eta=C_\eta\frac{\varepsilon}{\kappa\sqrt L},\qquad
--   Q_{\mathrm{SELECT}},Q_{P_B}\le C_{\mathrm{calls}}\kappa\sqrt L.
--   \]
--   The reduction outputs a success flag with probability at least \(1/2\). Conditional on success, its system output is the pure state whose vector representative is the normalized action of the actually simulated Fourier block on \(|b\rangle\), and
--   \[
--   \bigl\||\widetilde x\rangle-|x\rangle\bigr\|_2\le\varepsilon.
--   \]
--   This representative is fixed by the Fourier block; the error is not minimized over global phases. Failure output is unrestricted.
--
--   2. If \(A\) has at most \(d\) nonzero entries in each row and column, with \(1\le d\le N\), and \(P_A\) supplies both the in-place column-location oracle and the XOR entry oracle of equations (1)–(2), then there is a concrete sparse implementation with the same output guarantee and worst-case bounds
--   \[
--   Q_{P_A}\le C_A d\kappa^2L^{5/2},\qquad
--   Q_{P_B}\le C_{\mathrm{calls}}\kappa\sqrt L,\qquad
--   G_{\mathrm{external}}\le C_Gd\kappa^2L^{5/2}\bigl(\log N+L^{5/2}\bigr).
--   \]
--   The sum \(Q_{P_A}\) counts the two matrix-oracle operations separately and then adds them. Short columns may be padded with zero entries, the location lists need not be sorted, and injectivity of each in-place location map is required. Entries use a public ordinary signed binary complex-number format. This is the exact-entry branch of the paper's access model; sufficiently accurate finite-precision access is covered through the simulator error budget. No controlled access to the input black boxes is assumed. External gates exclude internal implementations of \(P_A\) and \(P_B\); inlining either subroutine adds its per-call gate cost times its corresponding number of calls.
--
--   The bounds establish logarithmic dependence on output precision for quantum state preparation. The number of calls is bounded in the worst case using a finite capped amplification routine.
--
--   **Formalization Note** The Lean conclusion includes both clauses in one theorem and fixes the reduction and sparse circuits before quantifying over hidden inputs. The preparation-time polynomial and binary format are public parameters. Successful output is represented by a subnormalized pure density matrix together with its explicitly specified vector representative and direct vector error. Invalid qubit padding cannot count as successful output.
--
--   **Correction to the printed source.**
--
--   Printed: Page 8 says a worst-case amplification guarantee needs an 'upper bound on the probability q'; page 15 writes 'τ := y_J y_K'.
--
--   Corrected: Use a known positive lower bound on q for capped amplification, as Corollary 10 does, and read the maximum evolution time as y_J z_K.
--
--   Reason: The required amplification work grows when q decreases; Corollary 10 provides q bounded below using known coefficient mass. The Fourier times are y_j z_k in (18), (31), (52); y_K is not the defined z cutoff.
-- source:
--   Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, Theorem 3 (Fourier approach), PDF p. 4. https://arxiv.org/abs/1511.02306v2 . PDF SHA-256: 3b184d2cf07b46e85fdc905aca12acae44b0ab9a6bfaec7565b3393ffd26de69.

import Definitions.Def_QAlgorithms_Defs_CKSFourierPrograms
import Definitions.Def_QAlgorithms_Defs_RetainedQueryPrograms
import Definitions.Def_QAlgorithms_Papers_RoadmapA10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.RoadmapA10

open QAlgorithms

attribute [local instance] Classical.propDecidable




















/-- Theorem 3 (Fourier approach), CKS arXiv:1511.02306v2, PDF/printed p.4; Problem 1
and access promises pp.2–3; coherent SELECT pp.7–8,12; gate calculation p.15.
Both nonsparse reduction and sparse specialization are asserted. Constants precede all
varying parameters; algorithms precede hidden inputs. Approximation and amplification are
conclusions. The p.15 typo tau = y_J y_K is read as y_J z_K, as in (18),(31),(52).
The p.8 printed "upper bound on the probability q" is read as a positive lower bound,
as required by the inverse-square-root cost and the worst-case cap in Corollary 10.
P_B acts on the state register, as in pp.2–3,8. An arbitrary extra preparation register
would require extra gates for the zero-state reflection, which (54) does not budget.
The namespace follows this unit's explicit module contract. -/
theorem fourier_qlsp :
    ∃ Ccalls Ctime Cprecision Cqueries Cgates : ℝ,
      0 < Ccalls ∧ 0 < Ctime ∧ 0 < Cprecision ∧ 0 < Cqueries ∧ 0 < Cgates ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
    ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ (N : ℕ) (hN : 0 < N) (kappa eps : ℝ), 1 ≤ kappa → 0 < eps → eps ≤ eps0 →
      threshold ≤ kappa / eps →
    ∀ (prepBound : Polynomial ℕ),
    let w : ℕ := 0
    ∃ G : CKSFourier.Grid,
      (∀ j k, |G.y j * G.z k| ≤ Ctime * kappa * precisionLog kappa eps) ∧
    ∃ reductions : (s : ℕ) → FourierReduction N w s G,
      (∀ s, ∀ (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A) (hpromise : MatrixPromise A kappa),
        ∀ (bvec : EuclideanSpace ℂ (Fin N)) (hb : bvec ≠ 0),
        ∀ PB : Matrix (Qubits (Nat.clog 2 N + w)) (Qubits (Nat.clog 2 N + w)) ℂ,
          LinearSystemAccess.IsWorkspaceStatePrep bvec PB →
          (∃ c : Circuit oneTwoQubitGateSet (Nat.clog 2 N + w),
            c.unitary = PB ∧ c.size ≤ prepBound.eval (Nat.clog 2 N)) →
        ∀ V : Matrix ((G.Index × Fin N) × Qubits s) ((G.Index × Fin N) × Qubits s) ℂ,
          CKSFourier.IsCoherentSelectSimulation G A hpromise.1 s V
            (Cprecision * eps / (kappa * Real.sqrt (precisionLog kappa eps))) →
          let R := reductions s
          let O := reductionOracles V PB
          PureFlaggedOutput hN A hA bvec hb
            (normalizedVec (act (simulatedInverse G V) (normalizedVec bvec)))
            (RetainedOracle.retainedOutput R.layout R.program O (pureDensity R.start) true)
            (RetainedOracle.retainedOutput R.layout R.program O (pureDensity R.start) false) eps ∧
          ∀ k : Fin 2,
            (RetainedOracle.worstCaseQueries R.program O (fun j => if j = k then 1 else 0)
              (pureDensity R.start) : ℝ) ≤ Ccalls * kappa * Real.sqrt (precisionLog kappa eps)) ∧
      (∀ (d : ℕ), 1 ≤ d → d ≤ N → ∀ F : LinearSystemAccess.BinaryComplexFormat,
        ∃ s : ℕ, ∃ S : SparseImplementation N F.width w s G,
        ∀ (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A) (hpromise : MatrixPromise A kappa), IsSparse A d →
        ∀ (bvec : EuclideanSpace ℂ (Fin N)) (hb : bvec ≠ 0),
        ∀ PA : (k : Fin 2) → Matrix
          (Qubits (if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + F.width))
          (Qubits (if k = 0 then Nat.clog 2 N + Nat.clog 2 N else Nat.clog 2 N + Nat.clog 2 N + F.width)) ℂ,
          IsSparseAccessOracle A d F.decode (PA 0) (PA 1) →
        ∀ PB : Matrix (Qubits (Nat.clog 2 N + w)) (Qubits (Nat.clog 2 N + w)) ℂ,
          LinearSystemAccess.IsWorkspaceStatePrep bvec PB →
          (∃ c : Circuit oneTwoQubitGateSet (Nat.clog 2 N + w),
            c.unitary = PB ∧ c.size ≤ prepBound.eval (Nat.clog 2 N)) →
          let J := simulationEmbedding G S.embedding
          let V := Jᴴ * S.simulation.unitary PA * J
          let O := sparseOracles F PA PB
          let R := reductions s
          CKSFourier.IsCoherentSelectSimulation G A hpromise.1 s V
            (Cprecision * eps / (kappa * Real.sqrt (precisionLog kappa eps))) ∧
          S.simulation.unitary PA * J = J * V ∧
          S.solver.output O =
            RetainedOracle.retainedOutput R.layout R.program (reductionOracles V PB)
              (pureDensity R.start) true ∧
          (S.solver.successState O S.solver.attempts).trace.re = (S.solver.output O).trace.re ∧
          PureFlaggedOutput hN A hA bvec hb
            (normalizedVec (act (simulatedInverse G V) (normalizedVec bvec)))
            (S.solver.output O)
            (RetainedOracle.retainedOutput R.layout R.program (reductionOracles V PB)
              (pureDensity R.start) false) eps ∧
          (S.solver.queries 0 + S.solver.queries 1 : ℝ) ≤
            Cqueries * d * kappa ^ 2 * (precisionLog kappa eps) ^ (5 / 2 : ℝ) ∧
          (S.solver.queries 2 : ℝ) ≤ Ccalls * kappa * Real.sqrt (precisionLog kappa eps) ∧
          (S.solver.gates : ℝ) ≤ Cgates * d * kappa ^ 2 *
            (precisionLog kappa eps) ^ (5 / 2 : ℝ) *
              (Real.log N + (precisionLog kappa eps) ^ (5 / 2 : ℝ))) := by sorry

end QAlgorithms.Papers.RoadmapA10
