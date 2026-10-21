-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_sum_rate_redundancy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.sum_rate_redundancy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:15:12.334645+00:00
-- url     : https://prove2.me/theorems/2e1f047c-9355-48da-b757-ad7be53d31a5
-- title:
--   The classical sum-rate constraint is redundant
-- statement:
--   Fix the Hadamard data of Section 2. Let $W,Z$ be arbitrary nonempty finite classical alphabets, let $p_{WZ}$ be any normalized joint distribution, and let $\sigma_A^z$ be any density operators, allowed to be mixed and depending only on $z$. Write
--
--   $$
--   \theta_{WZBC}=\sum_{w,z}p_{WZ}(w,z)\lvert w,z\rangle\langle w,z\rvert\otimes\mathcal N(\sigma_A^z).
--   $$
--
--   All information quantities use base-two von Neumann entropy. For nonnegative real rates $R_B,R_C$,
--
--   $$
--   R_B\le I(Z;B\mid W)_\theta\quad\text{and}\quad R_C\le I(W;C)_\theta
--   \quad\Longrightarrow\quad R_B+R_C\le I(Z;B)_\theta.
--   $$
--
--   Thus adding the sum-rate inequality does not change the two-constraint superposition region. This is the redundancy assertion, separate from the operational converse theorem.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 4, §3.2, unnumbered: redundancy of the classical sum-rate constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF p.4, Section 3.2, (14)–(18): the sum-rate bound (12) follows from
(10),(11). Inputs sigma_z may be mixed; their independence of w conditional
on z is built into ClassicalEnsemble, rather than assumed as an information identity. -/
theorem sum_rate_redundancy {a b c w z : ℕ} (H : HadamardData a b c)
    (S : ClassicalEnsemble w z a) (RB RC : ℝ) (hB : 0 ≤ RB) (hC : 0 ≤ RC)
    (bob_bound : RB ≤ classicalConditionalInfo S (bobChannel H))
    (charlie_bound : RC ≤ classicalLayerInfo S (charlieChannel H)) :
    RB + RC ≤ classicalTotalInfo S (bobChannel H) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
