-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_zeroErrorSDP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.zeroErrorSDP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:48:48.307901+00:00
-- url     : https://prove2.me/theorems/ad2e8faf-e78a-4251-a95a-faf416ddbfe1
-- title:
--   Theorem 17: zero-error SDPs and regularization
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite registers. The continuous NS∩PPT zero-error message relaxation is the attained maximum
--
--   $$M_{0,\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N)=\max\operatorname{Tr}S_A,$$
--
--   subject to $0\preceq U\preceq S_A\otimes I_B$, $\operatorname{Tr}_AU=I_B$, $\operatorname{Tr}[J_\mathcal N(S_A\otimes I_B-U)]=0$, and $0\preceq U^{T_B}\preceq S_A\otimes I_B$. Removing the PPT inequalities gives $M_{0,\mathrm{NS}}$. For either assisted class $\Omega$,
--
--   $$C_{0,\Omega}(\mathcal N)=\sup_{n\ge1}\frac1n\log_2M_{0,\Omega}(\mathcal N^{\otimes n}).$$
--
--   Here $M_{0,\Omega}=2^{C^{(1)}_\Omega(\mathcal N,0)}$ uses the continuous convention, not an assertion of an integer one-shot code size. This supplies both the zero-error SDP and its regularization.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 20, Theorem 17

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

/-- PDF pp.20–21, Theorem 17: attained zero-error SDP and its regularization;
true denotes NS∩PPT, false NS. The continuous message relaxation is explicit. -/
theorem zeroErrorSDP [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    ∀ ppt : Bool,
      IsGreatest (zeroValues ppt N) (zeroMessages ppt N) ∧
      zeroCapacity ppt N = sSup {r | ∃ n : ℕ, 0 < n ∧
        r = log2 (zeroMessages ppt (piSuperop (fun _ : Fin n => N))) / (n : ℝ)} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
