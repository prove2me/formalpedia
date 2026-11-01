-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_gram_blocks_and_transfer
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.gram_blocks_and_transfer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:32:33.797672+00:00
-- url     : https://prove2.me/theorems/9873b8d7-60e9-4fbe-93ce-69b0a8e92024
-- title:
--   Physical Gram blocks and spectral transfer
-- statement:
--   Let $N\ge1$ and $d\ge2$ be integers. Alice and Bob have $N$ ordered $d$-dimensional ports, and the input register $C$ has dimension $d$. Write $s=(d-1)/2$ and $|S\rangle=d^{-1/2}\sum_{m=-s}^s(-1)^{s-m}|s,m\rangle|s,-m\rangle$. Put $P_i=|S\rangle\langle S|_{A_iC}\otimes I_{\bar A_i}$, $\sigma_i=d^{-(N-1)}P_i$, and $\rho=\sum_i\sigma_i$. A resource filter $O$ gives $|\Psi_O\rangle=(O_A\otimes I_B)|S\rangle^{\otimes N}$ and obeys $\operatorname{tr}(O^\dagger O)=d^N$. Alice measures $AC$; Bob selects the reported port and discards the others. Entanglement fidelities are tested against a normalized reference-input singlet, with no correction on the selected port.
--
--   Fix an allowed total spin $j\le(N-1)s$ and magnetic number $m\in\{-j,\ldots,j\}$. Choose a base port $i_0$ and a real orthonormal basis $f_\alpha$ of the actual spin-$j$, magnetic-$m$ slice of its complement. Define the other complement bases by the physical swaps $i_0\leftrightarrow i$, as in Eq.(A4), and set $\xi_{i\alpha}=|S\rangle_{A_iC}\otimes f^{(i)}_\alpha$. Their actual Gram matrix $\Gamma_{i\alpha,k\beta}=\langle\xi_{i\alpha},\xi_{k\beta}\rangle$ is real symmetric and has
--   $$d\Gamma_{i\alpha,k\beta}=\begin{cases}d\delta_{\alpha\beta},&i=k,\\\delta_{\alpha\beta},&i\ne k\text{ and }(i=i_0\text{ or }k=i_0),\\\langle f_\alpha,V_{ik}f_\beta\rangle,&\text{otherwise},\end{cases}$$
--   where the last swap acts within the base complement. Writing $X$ for the matrix with columns $\xi_{i\alpha}$ gives $\rho(j,m)=d^{-(N-1)}XX^\dagger$. For every unit vector $c$ with $\Gamma c=\gamma c$, $\gamma\in\mathbb R$, the synthesized vector $\psi=Xc$ satisfies
--   $$\rho(j,m)\psi=\frac\gamma{d^{N-1}}\psi,\qquad\|\psi\|^2=\gamma,\qquad\gamma\le\frac{N+d-1}{d}.$$
--   For $\gamma>0$ it is nonzero; the vector identity also holds at zero. This gives the spectral interface of Appendix A without division by a zero port-component norm. Maximum-spin attainment is recorded in the exact spectral-maximum item.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 6, Appendix A Eqs.(A1)-(A7): Gram blocks and transfer to rho

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF p.6, Eqs.(A1)-(A7): Gram blocks, their physical spectral transfer,
and the eigenvalue bound. Basis vectors are real physical spin states;
A4's transported bases are defined, not free data. At gamma=0 the synthesized
vector is zero; a nonzero eigenvector is asserted only when gamma>0. -/
theorem gram_blocks_and_transfer (d N t r : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (ht : t ≤ (N - 1) * (d - 1)) (hparity : t % 2 = ((N - 1) * (d - 1)) % 2)
    (hr : r ≤ t) (i0 : Fin N) (A : Type*) [Fintype A] [DecidableEq A]
    (B : RealSpinBasis d N t r i0 A) :
    (∀ i k : Fin N, ∀ a b : A,
      (d : ℂ) * pbtGram B (i, a) (k, b) =
        if i = k then (d : ℂ) * (if a = b then 1 else 0)
        else if i = i0 ∨ k = i0 then (if a = b then 1 else 0)
        else (B.frameᴴ * complementSwap (d := d) i0 i k * B.frame) a b) ∧
    (∀ a b, (pbtGram B a b).im = 0) ∧ (pbtGram B).transpose = pbtGram B ∧
    rhoSpinMagnetic d N t r =
      ((d : ℂ) ^ (N - 1))⁻¹ • (gramFrame B * (gramFrame B)ᴴ) ∧
    (∀ (gamma : ℝ) (c : EuclideanSpace ℂ (Fin N × A)),
      QAlgorithms.IsState c → QAlgorithms.act (pbtGram B) c = (gamma : ℂ) • c →
      QAlgorithms.act (rhoSpinMagnetic d N t r) (gramSynthesis B c) =
        ((gamma : ℂ) / (d : ℂ) ^ (N - 1)) • gramSynthesis B c ∧
      ‖gramSynthesis B c‖ ^ 2 = gamma ∧
      (0 < gamma → gramSynthesis B c ≠ 0) ∧
      gamma ≤ ((N : ℝ) + d - 1) / d) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
