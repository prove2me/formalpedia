-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_depolarizingKrausRange
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.depolarizingKrausRange
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:27:51.368665+00:00
-- url     : https://prove2.me/theorems/ba0e1ad1-9523-4baa-bb5e-6fcfada4dfb2
-- title:
--   Exact depolarizing CPTP range and full Weyl Kraus system
-- statement:
--   Let $d\ge2$ be an integer and $\Phi_p(X)=(1-p)X+(p/d)\operatorname{Tr}(X)I$ for real $p$. This map is CPTP exactly when $0\le p\le d^2/(d^2-1)$. In that range choose any orthonormal basis and the cyclic Weyl system built in that basis $W_{ab}$ in dimension $d$, with $(a,b)=(0,0)$ the identity label. Set $a_0=1-p(d^2-1)/d^2$. Then the following Kraus family is normalized and represents $\Phi_p$:
--
--   $$A_{00}=\sqrt{a_0}\,I,\quad A_{ab}=\sqrt{p/d^2}\,W_{ab}\ ((a,b)\ne(0,0)),\qquad \Phi_p(X)=\sum_{a,b}A_{ab}XA_{ab}^*.$$
--
--   There are exactly $d^2-1$ nonidentity terms. Both endpoints and the allowed values $p>1$ are included. This pins the physical domain for the subsequent capacity formulas.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 7, §III, equations (23)–(24): depolarizing parameter range and Weyl Kraus form

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.7, (23)--(24): exact CPTP parameter interval and Weyl Kraus form,
including both endpoints and p>1. No last row or column is discarded. -/
theorem depolarizingKrausRange (d : ℕ) (hd : 2 ≤ d) (p : ℝ) :
    (IsChannel (QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p) ↔
      0 ≤ p ∧ p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) ∧
    (0 ≤ p → p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1) →
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        IsKrausFamily (weylDepolarizingKraus d (by omega) p U) ∧
        QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p =
          krausApply (weylDepolarizingKraus d (by omega) p U)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
