-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_explicit_sep_gap
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.explicit_sep_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:26:56.179969+00:00
-- url     : https://prove2.me/theorems/ce0fe838-b519-45ae-a13c-aee0ff5a5769
-- title:
--   An explicit separable instrument outside the LOCC closure
-- statement:
--   On two qubits let $P_b=|b\rangle\langle b|$, $A=\operatorname{diag}(1/\sqrt2,1)$, and define $\Pi_1=A\otimes P_0$, $\Pi_2=P_0\otimes A$, and $\Pi_3=P_1\otimes P_1$. Retain the three classical outcomes of $\mathcal K=(\mathcal E_1,\mathcal E_2,\mathcal E_3)$, where $\mathcal E_i(\rho)=\Pi_i\rho\Pi_i^\dagger$. Then
--   $$
--   \mathcal K\in\mathrm{SEP}\setminus\overline{\mathrm{LOCC}}.
--   $$
--   Closure uses the QC diamond distance without a factor of $1/2$ on the same input and output coordinates and classical labels. This gives the source's explicit operational separation of separable instruments from asymptotically approximable LOCC.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 15, §4.3, Eq.(23)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF pp.14–15, §4.3, Eq.(23): the explicit SEP instrument has positive operational
separation from LOCC in the sense that it is outside its QC-diamond closure. -/
theorem explicit_sep_gap :
    InSEP (fun _ : Fin 2 => 2) sepGapInstrument ∧
      ¬ InLOCCClosure (fun _ : Fin 2 => 2) sepGapInstrument := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end
