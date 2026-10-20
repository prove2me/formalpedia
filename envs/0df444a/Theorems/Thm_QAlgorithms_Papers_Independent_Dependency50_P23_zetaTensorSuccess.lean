-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_zetaTensorSuccess
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.zetaTensorSuccess
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:41:56.867132+00:00
-- url     : https://prove2.me/theorems/9a7215e2-7482-4a79-b540-51c020aa6eaf
-- title:
--   Unnumbered bound, Eqs.(49)–(50): ζ tensor-power success estimate
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite registers, and let $m,n\ge1$ be integers. Define $\widetilde f^+(\mathcal N,m)$ as the attained minimum of $\operatorname{Tr}S_B$ over Hermitian $V,S_B$ satisfying $V\succeq J_\mathcal N$ and $-mI_A\otimes S_B\preceq V^{T_B}\preceq mI_A\otimes S_B$. Then
--
--   $$f_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N^{\otimes n},m^n)\le\widetilde f^+(\mathcal N,m)^n.$$
--
--   Here success is optimized average decoding success over uniform messages with two-way NS and PPT assistance. This estimate underlies the zeta strong converse.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 17, Unnumbered bound, Eqs.(49)–(50)

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

/-- PDF p.17, Eqs.(49)–(50): second tensor-power success estimate. -/
theorem zetaTensorSuccess [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsLeast (zetaPlusValues N m) (zetaPlus N m) ∧
    nsSuccess true (piSuperop (fun _ : Fin n => N)) (m^n) ≤ (zetaPlus N m)^n := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
