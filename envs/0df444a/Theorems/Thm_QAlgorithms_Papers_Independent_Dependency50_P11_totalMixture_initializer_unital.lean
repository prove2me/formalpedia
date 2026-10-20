-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_totalMixture_initializer_unital
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.totalMixture_initializer_unital
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:41:09.789797+00:00
-- url     : https://prove2.me/theorems/4714f572-e59b-4801-b69d-4612e0f11c4c
-- title:
--   A maximally mixed memory induces a unital channel
-- statement:
--   Let $d,m\ge1$ and let $U$ be any unitary on $\mathbb C^m\otimes\mathbb C^d$. Initialize the memory in $I_m/m$, independently of the system, and define the induced one-use channel on operators by $\mathcal E(X)=\operatorname{Tr}_M[U((I_m/m)\otimes X)U^\dagger]$. Then
--
--   $$\mathcal E(I_d)=I_d.$$
--
--   The memory and system dimensions can differ. This is a one-use structural property; it requires no repeatability assumption.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 4, Section IV, maximally mixed memory paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section IV, PDF pp.4–5: a maximally mixed finite initializer induces a unital
one-use channel. No repeatability assumption, or equality of the dimensions, is required. -/
theorem totalMixture_initializer_unital {d m : ℕ} (hd : 0 < d) (D : MemoryDevice d m)
    (hInit : D.initial = totalMixture m) :
    IsUnital (fun X => traceLeft (jointStep D D.initial X)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
