-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_tensorSuccessBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.tensorSuccessBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:38:52.480008+00:00
-- url     : https://prove2.me/theorems/ceac51c9-4214-44d1-b279-ea44ae060e1a
-- title:
--   Proposition 10: tensor-product success bound
-- statement:
--   Let $\mathcal N:A\to B$ and $\mathcal G:C\to D$ be CPTP channels on nonzero finite registers, possibly of different dimensions. For integers $m,k,n\ge1$, define $f^+(\mathcal N,m)$ by the attained minimum of $\operatorname{Tr}Z_B$ subject to
--
--   $$-R\preceq J_\mathcal N^{T_B}\preceq R,\qquad -mI_A\otimes Z_B\preceq R^{T_B}\preceq mI_A\otimes Z_B.$$
--
--   Then
--
--   $$f_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N,m)\le f^+(\mathcal N,m),\quad f_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N\otimes\mathcal G,mk)\le f^+(\mathcal N,m)f^+(\mathcal G,k),$$
--
--   $$f_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N^{\otimes n},m^n)\le f^+(\mathcal N,m)^n.$$
--
--   Success uses uniform messages and bipartite NS∩PPT codes. These product bounds supply the exponential converses.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 14, Proposition 10

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF pp.14–15, Proposition 10: one use, two different channel dimensions,
and tensor powers. Both transposes in Eq.(41) are retained. -/
theorem tensorSuccessBound [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (N : Superop A B) (hN : IsChannel N) (G : Superop C D) (hG : IsChannel G)
    (m k n : ℕ) (hm : 0 < m) (hk : 0 < k) (hn : 0 < n) :
    IsLeast (plusValues N m) (fPlus N m) ∧
    nsSuccess true N m ≤ fPlus N m ∧
    nsSuccess true (tensorChannel N G) (m*k) ≤ fPlus N m * fPlus G k ∧
    nsSuccess true (piSuperop (fun _ : Fin n => N)) (m^n) ≤ (fPlus N m)^n := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
