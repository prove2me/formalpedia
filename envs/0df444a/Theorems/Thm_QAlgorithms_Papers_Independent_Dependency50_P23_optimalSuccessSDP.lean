-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_optimalSuccessSDP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.optimalSuccessSDP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:31:11.698735+00:00
-- url     : https://prove2.me/theorems/d03a9cc1-ae77-4c66-9beb-1bfa63b645cf
-- title:
--   Theorem 3: SDP characterization of optimal NS and NS∩PPT success
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite complex registers with fixed bases, and let $m\ge1$ be an integer. Messages are uniform, and $f_\Omega(\mathcal N,m)$ optimizes average decoding success over bipartite codes that are no-signalling in both directions, with PPT across Bob's input and output when $\Omega=\mathrm{NS}\cap\mathrm{PPT}$. With the unnormalized input-first Choi operator $J_\mathcal N$, the following maximum is attained:
--
--   $$f_\Omega(\mathcal N,m)=\max_{\rho,F}\operatorname{Tr}(J_\mathcal NF),\quad 0\preceq F\preceq\rho\otimes I_B,\quad\operatorname{Tr}\rho=1,\quad\operatorname{Tr}_AF=I_B/m.$$
--
--   For NS∩PPT impose additionally $0\preceq F^{T_B}\preceq\rho\otimes I_B$; for NS omit exactly these two inequalities. This identifies an operational integer-message optimum with a finite SDP, including $m=1$.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 6, Theorem 3

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

/-- PDF pp.6–8, Theorem 3: operational integer-message success equals the
attained SDP maximum, for NS (false) and NS∩PPT (true), including m=1. -/
theorem optimalSuccessSDP [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (m : ℕ) (hm : 0 < m) :
    ∀ ppt : Bool, IsGreatest (successValues ppt N m) (nsSuccess ppt N m) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
