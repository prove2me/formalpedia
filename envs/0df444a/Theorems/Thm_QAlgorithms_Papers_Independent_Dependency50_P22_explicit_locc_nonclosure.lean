-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_explicit_locc_nonclosure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.explicit_locc_nonclosure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:17:51.718359+00:00
-- url     : https://prove2.me/theorems/4b8fcb41-b341-4d40-afe8-5747a422d132
-- title:
--   An explicit two-qubit instrument in the closure of LOCC but outside LOCC
-- statement:
--   Consider two qubits held by Alice and Bob, with no additional shared entangled state. Let $P_b=|b\rangle\langle b|$ for $b\in\{0,1\}$, and let
--   $$
--   T_1=\operatorname{diag}(1/\sqrt3,1/\sqrt3),\qquad T_2=\operatorname{diag}(1/\sqrt6,\sqrt{2/3}).
--   $$
--   Define the labeled instrument $\mathcal J=(\mathcal E_{00},\mathcal E_{01},\mathcal E_{10})$ by $\mathcal E_{00}(\rho)=(P_1\otimes P_1)\rho(P_1\otimes P_1)$, $\mathcal E_{01}(\rho)=\sum_{i=1}^2(T_i\otimes P_0)\rho(T_i\otimes P_0)^\dagger$, and $\mathcal E_{10}(\rho)=\sum_{i=1}^2(P_0\otimes T_i)\rho(P_0\otimes T_i)^\dagger$. Then
--   $$
--   \mathcal J\in\overline{\mathrm{LOCC}}\setminus\mathrm{LOCC}.
--   $$
--   Here LOCC includes linked infinite-round protocols, and closure is measured by the diamond norm of the quantum-classical maps, without a factor of $1/2$. The classical labels and quantum outputs are both retained. This instrument witnesses nonclosedness on the smallest bipartite system.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 1, Abstract; §§4.1,4.3, Eqs.(10)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.1 and §§4.1,4.3, pp.10–15: the explicit two-qubit instrument is in the
LOCC closure but has no exact, even infinite-round, LOCC implementation. -/
theorem explicit_locc_nonclosure :
    InLOCCClosure (fun _ : Fin 2 => 2) eq11Instrument ∧
      ¬ InLOCC (fun _ : Fin 2 => 2) eq11Instrument := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end
