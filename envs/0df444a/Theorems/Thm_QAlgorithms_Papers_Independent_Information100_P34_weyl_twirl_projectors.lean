-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_weyl_twirl_projectors
-- name    : QAlgorithms.Papers.Independent.Information100.P34.weyl_twirl_projectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:55:21.922978+00:00
-- url     : https://prove2.me/theorems/ab0936af-9aaa-431e-ab3b-ad2868e0a6a9
-- title:
--   Lemma 21: Fourier–Weyl twirl eigenprojectors and dephasing relations
-- statement:
--   Fix an integer $d>0$, put $\omega=e^{2\pi i/d}$ and interpret every index cyclically modulo $d$. Define the shift $S|a\rangle=|a+1\rangle$, the clock $\Omega|a\rangle=\omega^a|a\rangle$, $W_{n,m}=S^n\Omega^m$, and $U_{n,m}=W_{n,m}\otimes F_d\overline{W_{n,m}}F_d^\dagger$. Put $|\Psi_{k,l}\rangle=d^{-1}\sum_{a,b}\omega^{a(b-k)-lb}|a,b\rangle$, $|\phi_k\rangle=d^{-1/2}\sum_b\omega^{bk}|b\rangle$, $\Pi_{k,l}=|\Psi_{k,l}\rangle\langle\Psi_{k,l}|$, $P_l=\sum_a|a\rangle\langle a|\otimes|\phi_{a-l}\rangle\langle\phi_{a-l}|$, and $Q_k=\sum_b|\phi_{b-k}\rangle\langle\phi_{b-k}|\otimes|b\rangle\langle b|$. Then
--
--   $$U_{n,m}=\omega^{nm}(W_{n,m}\otimes W_{m,n})=\sum_{k,l}\omega^{nk+lm}\Pi_{k,l},$$
--   $$\Delta_0\Pi_{k,l}=P_l/d=d^{-1}\sum_t\Pi_{t,l},\qquad\Delta_3\Pi_{k,l}=Q_k/d=d^{-1}\sum_t\Pi_{k,t}.$$
--
--   Each of the three projector families is self-adjoint, idempotent, pairwise orthogonal, and sums to the identity. These formulas diagonalize the Fourier-symmetry twirl.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 35, Lemma 21

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 21, Eqs.(C92-C93), PDF pp.35-37. All three complete orthogonal
families and both partial dephasings are included. -/
theorem weyl_twirl_projectors (d : ℕ) [NeZero d] :
    (∀ n m : ZMod d,
      weylPair n m = cyclicPhase d (n*m) • Matrix.kronecker (weyl n m) (weyl m n) ∧
      weylPair n m = ∑ k : ZMod d, ∑ l : ZMod d,
        cyclicPhase d (n*k + l*m) • jointProjector k l) ∧
    CompleteOrthogonal (fun kl : ZMod d × ZMod d => jointProjector kl.1 kl.2) ∧
    CompleteOrthogonal (leftProjector (d := d)) ∧
    CompleteOrthogonal (rightProjector (d := d)) ∧
    (∀ k l : ZMod d,
      dephaseInput (jointProjector k l) = (1 / (d : ℂ)) • leftProjector l ∧
      leftProjector l = ∑ t : ZMod d, jointProjector t l ∧
      dephaseOutput (jointProjector k l) = (1 / (d : ℂ)) • rightProjector k ∧
      rightProjector k = ∑ t : ZMod d, jointProjector k t) := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
