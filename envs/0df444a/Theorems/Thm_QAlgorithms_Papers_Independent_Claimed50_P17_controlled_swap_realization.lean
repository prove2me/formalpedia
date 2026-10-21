-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_controlled_swap_realization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.controlled_swap_realization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:00:38.207163+00:00
-- url     : https://prove2.me/theorems/af439959-6ede-45de-ae5f-0f63aa2170f8
-- title:
--   Controlled-SWAP identity for the printed instrument
-- statement:
--   Let $d\ge2$, and let $A,B,C,D$ be copies of $\mathbb C^d$ with a fixed basis. The unknown device is used once and implements $E_i(U)=U|i\rangle\langle i|U^\dagger$, returning only its classical label on $D$. Strategy data are independent of $U$. A cloning instrument is an array $R_{ij}\succeq0$ with $\sum_{ij}R_{ij}=I_D\otimes S_{ABC}$, $S\succeq0$, and $\operatorname{Tr}_C S=I_{AB}$. A learning instrument instead satisfies $\sum_{ij}R_{ij}=I_{ABD}\otimes\rho_C$, $\rho\succeq0$, $\operatorname{Tr}\rho=1$. All tensors are transported to wire order $((A,B),C),D$.
--
--   Write $G_{ij}^R(U)=[R_{ij}*E(U)]^T$ for the replica obtained with the unnormalized Choi convention and fixed-basis transpose. Its Haar score is
--   $$F(R)=\frac1{d^2}\int\sum_{ij}\operatorname{Re}\operatorname{Tr}\bigl[G_{ij}^R(U)(E_i(U)\otimes E_j(U))\bigr]\,dU.$$
--   The measure is normalized Haar on $SU(d)$; averaging over $U(d)$ gives precisely the same labeled-measurement law because scalar phases cancel.
--
--   Let $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$, $c=1/[9d(d+1)]$, and $|\psi\rangle=\sqrt c\,|+\rangle+| -\rangle/\sqrt2$. The control effects are
--   $$P_1=(1-2c)|+\rangle\langle+|,\quad P_2=|\psi\rangle\langle\psi|,\quad P_3=Z_{\pm}|\psi\rangle\langle\psi|Z_{\pm}.$$
--   Here $Z_{\pm}=|+\rangle\langle+|-|-\rangle\langle-|$ is explicitly the reflection in the $(+,-)$ basis (Pauli $X$ in the computational basis). This resolves the printed $\sigma_z$ basis ambiguity using Eqs.(64),(69). $|\psi\rangle$ is an effect vector, not a normalized input state. The three effects form a POVM. Postprocessing sends $(k,1)$ to $(k,k)$, $(k,2)$ to $(k,j)$ with $j\ne k$ uniform, and $(k,3)$ to $(j,k)$ with $j\ne k$ uniform; these kernels are nonnegative and sum to one. Let $Q_{ij}$ be the resulting POVM on the classical wire $D$ and control $L$.
--
--   Let $J_\pm|m\rangle=(\sum_a|a,m,a\rangle\pm\sum_a|m,a,a\rangle)/\sqrt{2(d\pm1)}$, $d_\pm=d(d\pm1)/2$, and $|\phi_m^\pm\rangle=\sqrt{1/(9d)}J_+|m\rangle\pm\sqrt{d_-/d}J_-|m\rangle$. Define the printed instrument by
--   $$R_{ii}=\frac{9d_+-1}{9d}\sum_m|J_+m\rangle\langle J_+m|\otimes|i\rangle\langle i|_D,$$
--   $$R_{ij}=\frac{\sum_m|\phi_m^+\rangle\langle\phi_m^+|\otimes|i\rangle\langle i|_D+\sum_m|\phi_m^-\rangle\langle\phi_m^-|\otimes|j\rangle\langle j|_D}{2(d-1)}\quad(i\ne j).$$
--   The unitary $U_{CS}$ routes $(A,B)$ to $(C,K)$ unchanged on control $0$ and exchanged on control $1$. With the control prepared in $|+\rangle$, one has
--   $$R_{ij}=|+\rangle\langle+|*|U_{CS}\rangle\!\rangle\langle\!\langle U_{CS}|*(Q_{ij}\otimes I_K).$$
--   The instrument is feasible for cloning. The identity is evaluated by an explicit coordinate contraction over the discarded wire $K$ and control indices. It specifies a realization without asserting optimality of these printed coefficients.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 8, §V A, Eqs.(64)–(69): controlled-SWAP realization identity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.8, Eqs.(64)-(69): the printed controlled-SWAP
realization identity and its full three-effect POVM and stochastic postprocessing.
Source basis correction: Eq.(66) prints sigma_z; use the explicit reflection
Z_pm=|+><+|-|-><-|, since computational Pauli Z fails the POVM identity sum.
The existing effect-vector formula and Eqs.(64),(69) select exactly this reflection.
All scalar coefficients are unchanged. No optimality of this network is asserted. -/
theorem controlled_swap_realization (d : ℕ) (hd : 2 ≤ d) :
    IsPOVM (controlPOVM d) ∧
    (∀ k : Fin d, ∀ n : Fin 3,
      (∀ i j, 0 ≤ postprocess k n i j) ∧ (∑ i, ∑ j, postprocess k n i j) = 1) ∧
    (controlledSwap d).conjTranspose * controlledSwap d = 1 ∧
    IsReplicationStrategy .cloning (printedInstrument d) ∧
    printedInstrument d = networkInstrument d := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
