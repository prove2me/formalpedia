-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_dualSuccessSDP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.dualSuccessSDP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:32:32.275556+00:00
-- url     : https://prove2.me/theorems/ca71a664-c31c-4c31-b308-f3ab58176389
-- title:
--   Unnumbered remark, Eq.(22): dual success SDP
-- statement:
--   Let $\mathcal N:A\to B$ be a finite CPTP channel with nonzero input and output dimensions, and $m\ge1$ an integer. Let $J_\mathcal N$ be its unnormalized input-first Choi matrix, and let $T_B$ denote output partial transpose. For uniform messages, the NS∩PPT optimum is the attained minimum
--
--   $$f_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N,m)=\min\left\{t+\frac{\operatorname{Tr}S_B}{m}: J_\mathcal N\preceq X+I_A\otimes S_B+(W-Y)^{T_B},\ \operatorname{Tr}_B(X+W)\preceq tI_A\right\},$$
--
--   where $t$ is real, $S_B$ is Hermitian, and $X,Y,W\succeq0$. Setting $Y=W=0$ gives the NS dual. Thus both primal and dual optima agree, with attainment; $S_B$ is not required to be positive.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 8, Unnumbered remark, Eq.(22)

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

/-- PDF p.8, Eq.(22): both success duals attain their minimum and agree with
operational success. For NS, Y=W=0 is part of SuccessDualFeasible. -/
theorem dualSuccessSDP [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (m : ℕ) (hm : 0 < m) :
    ∀ ppt : Bool, IsLeast (dualValues ppt N m) (nsSuccess ppt N m) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
