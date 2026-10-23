-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_ch17_H_inversion
-- name    : RamanujanLostNotebook.PartV.ch17_H_inversion
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-09T00:22:22.348019+00:00
-- url     : https://prove2.me/theorems/bedb7350-c83f-470d-abd7-07a8e7661760
-- title:
--   Inversion law for H
-- statement:
--   For Im(tau)>0, put q=exp(2 pi i tau), F=(exp(-2 pi i tau/24) f3(q), 2 exp(2 pi i tau/3) omega3(exp(pi i tau)), 2 exp(2 pi i tau/3) omega3(-exp(pi i tau))). Here f3(q)=sum_{n>=0} q^(n^2)/(-q;q)_n^2 and omega3(q)=sum_{n>=0} q^(2n(n+1))/(q;q^2)_(n+1)^2; (a;q)_n=product_{j=0}^{n-1}(1-aq^j). Let g0(z)=sum_{n in Z}(-1)^n(n+1/3) exp(3 pi i (n+1/3)^2 z), g1(z)=-sum_{n in Z}(n+1/6) exp(3 pi i (n+1/6)^2 z), and g2(z)=sum_{n in Z}(n+1/3) exp(3 pi i (n+1/3)^2 z). Write S(v0,v1,v2)=(v1,v0,-v2). Define G(tau)=2 i sqrt(3) integral_{-conj(tau)}^{i infinity} S(g(z))/sqrt(-i(z+tau)) dz along the vertical ray, with principal square root. Set H=F-G.   For every Im(tau)>0, H(-1/tau)/sqrt(-i tau)=S(H(tau)). Differs from the printed source: Equation (17.2.1), p. 365 omits the square on the f3 denominator. We normalize f3 to the book's earlier third-order definition (2.1.1), using the unchanged shared mockF3 with the squared denominator. The unsquared series is the fifth-order f0 and differs from f3 already at q^2 (coefficients -1 and -2); the squared form is also the one in Bringmann and Ono's eq. (1.6) (author manuscript of Invent. Math. 165 (2006)), and with the unsquared series the inversion law fails numerically, while the translation law holds with either series (tau -> tau+1 fixes q). Correction ours. The printed inversion factor is 1/sqrt(-tau) (p. 367); we use 1/sqrt(-i tau), principal branch. With the printed factor the law fails numerically by the relative amount |1-exp(i pi/4)|=0.765 at four test points; with sqrt(-i tau) it holds to about 1e-42 there (one point with |q|=0.53). For H this is the factor of Zwegers' theorem as restated by Bringmann and Ono (author manuscript of Invent. Math. 165 (2006), Theorem 2.1); for G it is the factor for which Theorem 17.2.1 follows from Lemmas 17.2.1 and 17.2.3 by subtraction. Correction ours; numerical evidence and a cited restatement, not a proof.
--
--   **Discrepancy from the printed source.** Equation (17.2.1), p. 365 omits the square on the f3 denominator. We normalize f3 to the book's earlier third-order definition (2.1.1), using the unchanged shared mockF3 with the squared denominator. The unsquared series is the fifth-order f0 and differs from f3 already at q^2 (coefficients -1 and -2); the squared form is also the one in Bringmann and Ono's eq. (1.6) (author manuscript of Invent. Math. 165 (2006)), and with the unsquared series the inversion law fails numerically, while the translation law holds with either series (tau -> tau+1 fixes q). Correction ours. The printed inversion factor is 1/sqrt(-tau) (p. 367); we use 1/sqrt(-i tau), principal branch. With the printed factor the law fails numerically by the relative amount |1-exp(i pi/4)|=0.765 at four test points; with sqrt(-i tau) it holds to about 1e-42 there (one point with |q|=0.53). For H this is the factor of Zwegers' theorem as restated by Bringmann and Ono (author manuscript of Invent. Math. 165 (2006), Theorem 2.1); for G it is the factor for which Theorem 17.2.1 follows from Lemmas 17.2.1 and 17.2.3 by subtraction. Correction ours; numerical evidence and a cited restatement, not a proof.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 17, Theorem 17.2.1, p. 367.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17F
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17G
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17GTerm
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17H
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17S
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17Theta
import Definitions.Def_RamanujanLostNotebook_PartV_ch17_ch17ThetaTerm
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockF3
import Definitions.Def_RamanujanLostNotebook_PartV_shared_mockOmega3
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPoch

namespace RamanujanLostNotebook.PartV
theorem ch17_H_inversion (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ c : Fin 3, ch17H (-1/τ) c / Complex.sqrt (-Complex.I * τ) = ch17S (ch17H τ) c := by sorry
end RamanujanLostNotebook.PartV
