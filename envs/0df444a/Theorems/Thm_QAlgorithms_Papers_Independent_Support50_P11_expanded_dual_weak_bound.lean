-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_expanded_dual_weak_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P11.expanded_dual_weak_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:06:00.882731+00:00
-- url     : https://prove2.me/theorems/6d6417e3-c085-4c8d-9a7a-4f6e727e9751
-- title:
--   §IV (42)–(44): expanded Lagrange dual and weak-dual bound
-- statement:
--   Let $\mathcal N:A'\to B$ be finite CPTP, $K\ge1$, and select NS and/or PPTp with flags $s,p$. Fix $\mu\in\mathbb R$, Hermitian $W$ on $B$, and PSD multipliers $X,Y,V$ on $A'B$. Require $W=0$ without NS and $Y=V=0$ without PPTp. The expanded dual has objective $\mu+\operatorname{Tr}(W)/K^2$ and constraints
--   $$N^T+\Gamma_B(Y-V)\preceq X+I_{A'}\otimes W,\qquad
--   \operatorname{Tr}_B\bigl(X+(Y+V)/K\bigr)\preceq\mu I_{A'}.$$
--   These constraints are equivalent to the source's unreduced Lagrangian being at most that objective for every PSD pair $(\rho,\Lambda)$, without normalization imposed on $\rho$. Each dual feasible tuple satisfies
--   $$\operatorname{Re}\operatorname{Tr}(N^T\Lambda)\le\mu+\operatorname{Tr}(W)/K^2$$
--   for every primal feasible pair and also bounds $F^{\Omega_{s,p}}(\mathcal N,K)$. This is the genuine expanded Lagrange dual and weak-dual bound; $Y,V$ remain separate variables.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 7, §IV (42)–(44): expanded Lagrange dual and weak-dual bound

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

/-- PDF pp.7--8, (42)--(44): every expanded-dual feasible point bounds every
primal point and the operational optimum. Y,V remain independent PSD multipliers;
without PPT they both vanish, and without NS the Hermitian W vanishes. -/
theorem expanded_dual_weak_bound
    (N : Superop I O) (hN : IsChannel N) (K : ℕ) (hK : 0 < K)
    (s p : Bool) (hflags : s = true ∨ p = true) (mu : ℝ) (W : Matrix O O ℂ)
    (X Y V : Matrix (I × O) (I × O) ℂ)
    (hW : W.IsHermitian) (hX : X.PosSemidef) (hY : Y.PosSemidef) (hV : V.PosSemidef)
    (hzeroW : s = false → W = 0) (hzeroYV : p = false → Y = 0 ∧ V = 0) :
    (ExpandedDualFeasible N K s p mu W X Y V ↔
      ∀ (rho : Matrix I I ℂ) (L : Matrix (I × O) (I × O) ℂ), rho.PosSemidef → L.PosSemidef →
        lagrangian N K mu W X Y V L rho ≤ mu + W.trace.re / (K : ℝ)^2) ∧
    (ExpandedDualFeasible N K s p mu W X Y V →
      (∀ rho L, Primal K s p rho L → primalObjective N L ≤ mu + W.trace.re / (K : ℝ)^2) ∧
      optimalCodeFidelity (flagsClass s p) N K ≤ mu + W.trace.re / (K : ℝ)^2) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
