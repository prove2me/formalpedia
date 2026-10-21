-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P40_bellProtocol_averageFidelity
-- name    : QAlgorithms.Papers.Independent.Renew46.P40.bellProtocol_averageFidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:19:37.846577+00:00
-- url     : https://prove2.me/theorems/2a2d2a48-2dd6-4336-a3c4-54b9635f5fdc
-- title:
--   Haar-averaged transmission fidelity for arbitrary unitary corrections
-- statement:
--   Let $n\geq1$ and $H=\mathbb C^n$ with computational basis $|0\rangle,\ldots,|n-1\rangle$. Set $\omega=e^{-2\pi i/n}$, $h|j\rangle=|(j+1)\bmod n\rangle$, $g|j\rangle=\omega^j|j\rangle$, and $U_{st}=h^tg^s$. All labels below range over $\{0,\ldots,n-1\}^2$. Write $\overline A$ for entrywise conjugation and $A^\dagger$ for adjoint. Define $|\Phi\rangle=n^{-1/2}\sum_j|jj\rangle$ and $|\Phi_m\rangle=(I\otimes\overline{U_m})|\Phi\rangle$.
--
--   Let $\chi$ be any positive semidefinite trace-one resource on $H\otimes H$, with Alice's half first. For a fixed family of unitary matrices $T=(T_m)_m$, define $\Lambda_\chi(T)$ operationally: independently prepare $\rho\otimes\chi$ on registers $1,2,3$; project registers $1,2$ onto the Bell basis, communicate outcome $m$, apply $T_m^\dagger$ on register $3$, trace out registers $1,2$, and sum the unnormalized branches. The correction family may depend on $\chi$ and the outcome but is independent of the unknown input.
--
--   Let $f_\chi(T)$ be the mean of $\langle\psi|\Lambda_\chi(T)(|\psi\rangle\langle\psi|)|\psi\rangle$ over normalized pure inputs, using the probability Haar law (equivalently the orbit of $|0\rangle$ under Haar-distributed unitaries). Then
--
--   $$
--   f_\chi(T)=\frac1{n(n+1)}\sum_m\langle\Phi|\bigl(I\otimes(T_mU_m^\dagger)^\dagger\bigr)\chi\bigl(I\otimes T_mU_m^\dagger\bigr)|\Phi\rangle+\frac1{n+1}.
--   $$
--
--   This formula gives the mean transmission fidelity for each correction family before optimization. It also holds for $n=1$, when both sides equal one.
--
--   **Formalization Note** The statement uses the accepted normalized Haar integral, whose integrability follows from the channel property. The adjoints match printed Eq.(13); the singular $n^2-1$ denominator in the background twirling calculation is not used in the statement.
-- source:
--   Optimal Teleportation Based on Bell Measurement, arXiv:quant-ph/0208015v2, PDF p. 5, Theorem 2, Eq.(13): Haar-averaged transmission fidelity for any correction family

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P40

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Renew46.P40

/-- Theorem 2, Eq.(13), PDF pp.5–6 of arXiv:quant-ph/0208015v2.
The true normalized Haar mean of pure-input survival fidelity has this value for every
unitary correction family. The overlap uses W_m=T_m U_m dagger; its left factor is
W_m dagger and its right factor is W_m. There is no correction to the printed Eq.(13).
Positive dimension includes n=1; the singular coefficients of the proof's Eq.(12)
are not assumptions of this statement. -/
theorem bellProtocol_averageFidelity (n : ℕ) (hn : 0 < n) (chi : ResourceMatrix n)
    (hchi : IsDensityMatrix chi) (T : BellLabel n → QuditMatrix n)
    (hT : IsCorrectionFamily T) :
    QuditFidelity.averageFidelity n hn (teleportation hn chi T) =
      (1 / ((n : ℝ) * ((n : ℝ) + 1))) *
        (∑ m : BellLabel n, entangledOverlap hn chi (T m * (bellWeyl m)ᴴ)) +
          1 / ((n : ℝ) + 1) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P40

end
