-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_exact_qubit_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.exact_qubit_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:54:50.29075+00:00
-- url     : https://prove2.me/theorems/994a6de2-1a66-49ea-ab43-9910e82d650e
-- title:
--   Appendix C / Eqs.(68)–(70): exact qubit fidelity
-- statement:
--   For integers $1\le k\le N$, let $F_2(N,k)$ be the fixed-resource qubit MPBT entanglement fidelity with completed SRM. Put $m=N-k$. For lower-row lengths $0\le r\le\lfloor m/2\rfloor$ and $0\le t\le\lfloor N/2\rfloor$, set $h_{r,t}=\binom{k}{t-r}-\binom{k}{N-r-t+1}$, with binomial coefficients zero outside their integer range. Then
--
--   $$F_2(N,k)=2^{-N-2k}\sum_{r=0}^{\lfloor m/2\rfloor}\left(\sum_{\substack{0\le t\le\lfloor N/2\rfloor\\r\le t\le r+k\\r+t\le N}}h_{r,t}\sqrt{\frac{(N-2t+1)^2N!}{t!(N-t+1)!}}\right)^2.$$
--
--   This is Eq. (68) with $s=m/2-r$ and $j=N/2-t$, so spin parity is automatic. The erroneous simplification in Eq. (70) is not used.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 14, Appendix C / Eqs.(68)–(70): exact qubit fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.14, Eq.(68): exact completed-SRM qubit entanglement fidelity.
Eq.(70)'s denominator N+1 would need sqrt(N+1); Eq.(68) is used unchanged. -/
theorem exact_qubit_fidelity (N k : ℕ) (hk : 1 ≤ k) (hNk : k ≤ N) :
    mpbtFidelity 2 N k = qubitFidelityExpression N k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
