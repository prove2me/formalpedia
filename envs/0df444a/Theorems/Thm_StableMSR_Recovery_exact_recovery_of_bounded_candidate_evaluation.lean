-- Prove2me | Theorems.Thm_StableMSR_Recovery_exact_recovery_of_bounded_candidate_evaluation
-- name    : StableMSR.Recovery.exact_recovery_of_bounded_candidate_evaluation
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:40:05.220344+00:00
-- url     : https://prove2.me/theorems/bdc58f22-f44f-4268-a44e-97bbc7660a63
-- title:
--   Bounded correctness of the exhibited integer program suffices for Theorem 1.1
-- statement:
--   A uniform bound and exact tape correspondence for the one displayed integer command imply deterministic exact recovery for every fixed stability factor $\gamma>1$, with the original finite-program quantifiers, the mission runtime, and the fifth-power envelope near $\gamma=1$. This folds the canonically ordered regional writer and the full recovery dependency chain into one conditional theorem.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CandidateInterpreter
import Definitions.Def_StableMSR_Recovery_Execution
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

theorem StableMSR.Recovery.exact_recovery_of_bounded_candidate_evaluation (evaluated :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by sorry
