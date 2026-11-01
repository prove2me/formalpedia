-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P80_bp_error_updates
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P80.bp_error_updates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:58:01.015676+00:00
-- url     : https://prove2.me/theorems/8bb8e85e-fa68-4613-aa9e-9ba3c29ac43c
-- title:
--   B and P steps: conditional Pauli error transformations
-- statement:
--   Let independent input EPR pairs have Bell-diagonal Pauli noise with probabilities $q_X,q_Y,q_Z\ge0$, where $q_X+q_Y+q_Z\le1$, and put $q_I=1-q_X-q_Y-q_Z$. A B step applies the bilateral controlled-NOT to two pairs, measures the target pair in the $Z$ basis, and retains the control pair exactly when the two measurement outcomes agree. Let $p_S$ be its acceptance probability per two-pair block, and let $q^B_X,q^B_Y,q^B_Z$ be the conditional error probabilities of the retained pair. A P step applies the three-pair phase repetition-code procedure, corrects the surviving pair by $Z$ precisely when both relative phase syndromes disagree, and retains it for every syndrome. Write $q^P_X,q^P_Y,q^P_Z$ for its output error probabilities. Then
--
--   $$
--   \begin{aligned}
--   p_S&=1-2(q_X+q_Y)(1-q_X-q_Y),\\
--   q^B_X&=\frac{q_X^2+q_Y^2}{p_S},&
--   q^B_Y&=\frac{2q_Xq_Y}{p_S},&
--   q^B_Z&=\frac{2q_Iq_Z}{p_S},\\
--   q^P_X&=3q_I^2(q_X+q_Y)+6q_Iq_Xq_Z+3q_X^2q_Y+q_X^3,\\
--   q^P_Y&=6q_Iq_Yq_Z+3q_X(q_Y^2+q_Z^2)+3q_Yq_Z^2+q_Y^3,\\
--   q^P_Z&=3q_I(q_Y^2+q_Z^2)+6q_Xq_Yq_Z+3q_Y^2q_Z+q_Z^3.
--   \end{aligned}
--   $$
--
--   These transformations describe the effective noise after a purification round. Independence is an assumption of this calculation, rather than a restriction on the adversaries in the paper's separate QKD security results.
--
--   **Formalization Note** Both step maps are computed from branch amplitudes of the specified circuits and Born probabilities. They are not defined by the displayed polynomials.
-- source:
--   Proof of security of quantum key distribution with two-way classical communications, arXiv:quant-ph/0105121v2, PDF p. 22, Appendix C, equations (15)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P80

open scoped ComplexConjugate

/-- Appendix C, PDF p.22, Eqs.(15)--(22); physical steps are defined on
PDF pp.16,18. For independent Bell-diagonal noise, the circuit-derived B
and P outputs have exactly these Pauli rates. B survival is per two-pair
block, rather than the retained/input population fraction. -/
theorem bp_error_updates (q : PauliRates) (hq : IsPauliRates q) :
    bSurvival q = 1 - 2 * (q.qX + q.qY) * (1 - q.qX - q.qY) ∧
    (bStep q).qX = (q.qX ^ 2 + q.qY ^ 2) / bSurvival q ∧
    (bStep q).qY = 2 * q.qX * q.qY / bSurvival q ∧
    (bStep q).qZ = 2 * identityRate q * q.qZ / bSurvival q ∧
    (pStep q).qX = 3 * identityRate q ^ 2 * (q.qX + q.qY) +
      6 * identityRate q * q.qX * q.qZ + 3 * q.qX ^ 2 * q.qY + q.qX ^ 3 ∧
    (pStep q).qY = 6 * identityRate q * q.qY * q.qZ +
      3 * q.qX * (q.qY ^ 2 + q.qZ ^ 2) + 3 * q.qY * q.qZ ^ 2 + q.qY ^ 3 ∧
    (pStep q).qZ = 3 * identityRate q * (q.qY ^ 2 + q.qZ ^ 2) +
      6 * q.qX * q.qY * q.qZ + 3 * q.qY ^ 2 * q.qZ + q.qZ ^ 3 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P80

end
