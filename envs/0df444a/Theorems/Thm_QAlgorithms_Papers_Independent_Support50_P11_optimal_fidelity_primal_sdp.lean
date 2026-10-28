-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_optimal_fidelity_primal_sdp
-- name    : QAlgorithms.Papers.Independent.Support50.P11.optimal_fidelity_primal_sdp
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:05:04.779851+00:00
-- url     : https://prove2.me/theorems/a746815f-ea7a-4675-8a64-653cdefdf1c3
-- title:
--   Corollary 4: optimal channel fidelity is the primal SDP
-- statement:
--   Let $\mathcal N:A'\to B$ be a finite CPTP channel and $K\ge1$. Select NS, PPTp, or their intersection using flags $s,p$ with at least one true. Let $\mathcal P_{s,p}$ consist of density matrices $\rho$ and operators $\Lambda$ satisfying $0\preceq\Lambda\preceq\rho\otimes I_B$, together with $\operatorname{Tr}_{A'}\Lambda=I_B/K^2$ when $s$ is true and $-\rho\otimes I_B/K\preceq\Gamma_B(\Lambda)\preceq\rho\otimes I_B/K$ when $p$ is true. For the unnormalized Choi matrix $N$,
--   $$F^{\Omega_{s,p}}(\mathcal N,K)=\max_{(\rho,\Lambda)\in\mathcal P_{s,p}}\operatorname{Re}\operatorname{Tr}(N^T\Lambda).$$
--   There is a maximizing feasible pair, and an actual code in the selected class attains the same value. The objective is linear and the constraints are affine equalities and PSD inequalities, giving the stated SDP. At $K=1$ its optimum is one.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 7, Corollary 4: optimal channel fidelity is the primal SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section Statements

variable {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]

/-- PDF p.7, Corollary 4: equality with the operational optimum and an attained
primal maximum, for each of NS, PPTp and their intersection, including K=1. -/
theorem optimal_fidelity_primal_sdp
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K)
    (s p : Bool) (hflags : s = true ∨ p = true) :
    ∃ rho : Matrix I I ℂ, ∃ L : Matrix (I × O) (I × O) ℂ,
      Primal K s p rho L ∧ optimalCodeFidelity (flagsClass s p) N K = primalObjective N L ∧
      (∀ rho2 L2, Primal K s p rho2 L2 → primalObjective N L2 ≤ primalObjective N L) ∧
      (∃ Z : Superop (Fin K × O) (I × Fin K),
        IsForwardCode K (flagsClass s p) Z ∧
        channelFidelity K (link K N Z) = primalObjective N L) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
