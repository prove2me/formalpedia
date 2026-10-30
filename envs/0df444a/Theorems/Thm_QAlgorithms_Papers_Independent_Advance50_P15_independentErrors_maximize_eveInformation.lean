-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P15_independentErrors_maximize_eveInformation
-- name    : QAlgorithms.Papers.Independent.Advance50.P15.independentErrors_maximize_eveInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:25:24.844016+00:00
-- url     : https://prove2.me/theorems/971452be-2862-4212-b884-0da347c260ab
-- title:
--   Independent errors attain Eve’s maximum and its explicit entropy value
-- statement:
--   Let $m\ge1$, $0\le p\le1/2$, and $0\le q\le1$. For $t\in[0,p]$, take $m$ independent copies of the Bell-diagonal pair state with weights $1+t-2p,p-t,p-t,t$ on $\Phi^+,\Phi^-,\Psi^+,\Psi^-$, respectively. Eve holds its entire channel purification. Alice adds independent Bernoulli$(q)$ noise, keeps its purifying register private, retains the first noisy bit $A$, and publicly announces all repetition syndromes $V$. No blocks are discarded. Write $\chi_m(p,q,t)=I(A;EV)$ for the mutual information in the resulting state, using base-2 entropy. Then
--
--   $$
--   \chi_m(p,q,t)\le \chi_m(p,q,p^2)
--   \qquad\text{for every }t\in[0,p].
--   $$
--
--   Thus independent bit and phase errors attain the maximum; uniqueness is not asserted. The comparison concerns product copies of one allowed pair state, rather than arbitrary correlated multi-pair attacks.
--
--   **Formalization Note** The conditional density matrices are computed explicitly from the Bell purification and the private noise mixture. Eve’s register includes a classical copy of $V$, and no zero-mass conditional error distribution is formed.
--
--   At the independent-error state the information also has the explicit value
--
--   $$
--   \chi_m(p,q,p^2)=S\!\left(\tfrac12\rho_{p,q}^{\otimes m}
--   +\tfrac12 Z^{\otimes m}\rho_{p,q}^{\otimes m}Z^{\otimes m}\right)-mS(\rho_{p,q}),
--   $$
--
--   where $S$ is von Neumann entropy in bits, $Z=\operatorname{diag}(1,-1)$,
--   $\rho_{p,q}=(1-q)|\phi_+\rangle\langle\phi_+|+q|\phi_-\rangle\langle\phi_-|$,
--   and $|\phi_\pm\rangle=\sqrt{1-p}|0\rangle\pm\sqrt p|1\rangle$.
-- source:
--   Structured Codes Improve the Bennett-Brassard-84 Quantum Key Rate, arXiv:quant-ph/0607018v2, PDF p. 3, Proof of Theorem 1, Eq. (8)–(10)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P15

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P15

open QAlgorithms

open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Smith--Renes--Smolin, PDF p.3, proof of Theorem 1, Eq.(8)--(10): over
all permitted single-pair laws, Eve's information is maximized at t=p^2,
where it equals the displayed phase-mixture entropy minus m S(rho_(p,q)).
The public syndrome is retained; no uniqueness of the maximum is asserted. -/
theorem independentErrors_maximize_eveInformation
    (k : ℕ) (p q t : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ p) :
    eveInformation k p q t ≤ eveInformation k p q (p ^ 2) ∧
      eveInformation k p q (p ^ 2) =
        vnEntropy (repetitionPhaseMixture (k + 1) p q) -
          ((k + 1 : ℕ) : ℝ) * vnEntropy (phaseDensity p q) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P15

end
