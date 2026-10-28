-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_primal_feasibility_iff
-- name    : QAlgorithms.Papers.Independent.Support50.P11.primal_feasibility_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:04:10.791949+00:00
-- url     : https://prove2.me/theorems/13e81b07-5fbb-4039-b951-8d7b0f889d39
-- title:
--   Theorem 3: exact primal feasibility characterization
-- statement:
--   Fix a finite CPTP channel $\mathcal N:A'\to B$, a density matrix $\rho$ on $A'$, a positive integer $K$, a real number $f$, and Boolean flags $s,p$, at least one true, selecting NS and PPTp respectively. Let $N$ be the unnormalized Choi matrix in reference–output order and $\Gamma_B$ ordinary partial transpose on $B$. A forward-assisted code with the selected properties, average input exactly $\rho$, and channel fidelity exactly $f$ exists if and only if: for $K=1$, $f=1$; for $K\ge2$, an operator $\Lambda$ exists with
--   $$f=\operatorname{Re}\operatorname{Tr}(N^T\Lambda),\quad 0\preceq\Lambda\preceq\rho\otimes I_B,$$
--   $$s\Rightarrow\operatorname{Tr}_{A'}\Lambda=I_B/K^2,\qquad
--   p\Rightarrow-\rho\otimes I_B/K\preceq\Gamma_B(\Lambda)\preceq\rho\otimes I_B/K.$$
--   All comparisons are Loewner inequalities. This retains both directions and the prescribed input state. The scalar branch corrects the printed proof's division by $K^2-1$.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 6, Theorem 3: exact primal feasibility characterization

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

/-- PDF pp.6--7, Theorem 3, (31)--(35). The proof divides by K^2-1;
the printed scalar boundary is corrected to f=1 at K=1. The specified rho is retained. -/
theorem primal_feasibility_iff
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K)
    (s p : Bool) (hflags : s = true ∨ p = true)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (f : ℝ) :
    (∃ Z : Superop (Fin K × O) (I × Fin K),
      IsForwardCode K (flagsClass s p) Z ∧ codeAverageInput K Z = rho ∧
      channelFidelity K (link K N Z) = f) ↔
    (if K = 1 then f = 1 else
      ∃ L : Matrix (I × O) (I × O) ℂ, Primal K s p rho L ∧ f = primalObjective N L) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
