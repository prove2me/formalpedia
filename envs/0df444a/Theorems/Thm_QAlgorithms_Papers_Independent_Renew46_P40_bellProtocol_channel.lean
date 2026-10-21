-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P40_bellProtocol_channel
-- name    : QAlgorithms.Papers.Independent.Renew46.P40.bellProtocol_channel
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:18:52.698224+00:00
-- url     : https://prove2.me/theorems/e3859f1e-6571-4d08-bb44-d3d8af1c2a2a
-- title:
--   Bell-measurement teleportation is a channel with the corrected Bell expansion
-- statement:
--   Let $n\geq1$ and $H=\mathbb C^n$ with computational basis $|0\rangle,\ldots,|n-1\rangle$. Set $\omega=e^{-2\pi i/n}$, $h|j\rangle=|(j+1)\bmod n\rangle$, $g|j\rangle=\omega^j|j\rangle$, and $U_{st}=h^tg^s$. All labels below range over $\{0,\ldots,n-1\}^2$. Write $\overline A$ for entrywise conjugation and $A^\dagger$ for adjoint. Define $|\Phi\rangle=n^{-1/2}\sum_j|jj\rangle$ and $|\Phi_m\rangle=(I\otimes\overline{U_m})|\Phi\rangle$.
--
--   Let $\chi$ be any positive semidefinite trace-one resource on $H\otimes H$, with Alice's half first. For a fixed family of unitary matrices $T=(T_m)_m$, define $\Lambda_\chi(T)$ operationally: independently prepare $\rho\otimes\chi$ on registers $1,2,3$; project registers $1,2$ onto the Bell basis, communicate outcome $m$, apply $T_m^\dagger$ on register $3$, trace out registers $1,2$, and sum the unnormalized branches. The correction family may depend on $\chi$ and the outcome but is independent of the unknown input.
--
--   Put $c_{ab}=\langle\Phi_a|\chi|\Phi_b\rangle$. The operational map is completely positive and trace preserving, and for every density matrix $\rho$ on $H$,
--
--   $$
--   \Lambda_\chi(T)(\rho)=\frac1{n^2}\sum_{a,b}c_{ab}\sum_m T_m^\dagger\overline{U_a}U_m\rho U_m^\dagger\overline{U_b}^{\dagger}T_m.
--   $$
--
--   This identifies the channel of the entire fixed Bell protocol, including arbitrary mixed and separable resources.
--
--   **Formalization Note** This is the disclosed correction of printed Eq.(7): its resource-index factors $U_a,U_b^\dagger$ are replaced by $\overline{U_a},\overline{U_b}^{\dagger}$, as forced by the operator definition in Eq.(4). The measurement-index factors remain unchanged. The protocol is defined by projective measurement and partial trace, independently of this expansion.
-- source:
--   Optimal Teleportation Based on Bell Measurement, arXiv:quant-ph/0208015v2, PDF p. 3, Theorem 1, Eq.(7): channel of the Bell-measurement protocol with arbitrary unitary corrections

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P40

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Renew46.P40

/-- Theorem 1, Eq.(7), PDF pp.3–5 of arXiv:quant-ph/0208015v2.
The operational measurement/correction map is CPTP and has the stated Bell expansion.
SOURCE CORRECTION (trap 30, Q11): the printed resource factors U_a and U_b dagger
are replaced by entrywise-conjugate U_a and its counterpart for b, as forced by the
operator equality in Eq.(4). Outcome factors U_m are unchanged. See HARD.md.
The correction family is fixed before every density input; no entanglement premise is added. -/
theorem bellProtocol_channel (n : ℕ) (hn : 0 < n) (chi : ResourceMatrix n)
    (hchi : IsDensityMatrix chi) (T : BellLabel n → QuditMatrix n)
    (hT : IsCorrectionFamily T) :
    IsChannel (teleportation hn chi T) ∧
      ∀ rho : QuditMatrix n, IsDensityMatrix rho →
        teleportation hn chi T rho = bellExpansion hn chi T rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P40

end
