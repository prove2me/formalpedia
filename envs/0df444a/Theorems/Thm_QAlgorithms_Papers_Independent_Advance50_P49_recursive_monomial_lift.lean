-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_recursive_monomial_lift
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.recursive_monomial_lift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:19:25.395406+00:00
-- url     : https://prove2.me/theorems/25a5676d-b18d-4553-b872-2e18ba563500
-- title:
--   Recursive explicit lift of all disjoint exchange-monomial Hamiltonians
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For real coefficient functions $h_l$ on ordered injective wire tuples, let $H=\sum_{l=2}^{2\lfloor n/2\rfloor}\sum_{\mathbf i}h_l(\mathbf i)R_{i_1i_2}\cdots R_{i_{l-1}i_l}$; there is no arbitrary identity term. Lift each standard monomial using
--   $$\widetilde Q_2=Q_2\otimes I,\qquad \widetilde Q_l=Q_l\otimes I-Q_{l-2}\otimes R_{ab}+\tfrac12\widetilde Q_{l-2}\quad(l\ge4),$$
--   then permute its data wires and extend linearly to the prescribed $\widetilde H$. It is Hermitian, has a finite real exchange Lie expression, and
--   $$\widetilde H(\psi\otimes|00\rangle)=(H\psi)\otimes|00\rangle\quad\text{for every }\psi.$$
--   For each physical even $l\ge4$, the difference $Q_l\otimes I-Q_{l-2}\otimes R_{ab}$ itself has a finite exchange Lie expression. The statement retains I35–I36: in the four-term I32 template, replace its four first exchanges $R_{12},R_{23},R_{13},R_{35}$ by $T(R_{12}-R_{45}),T(R_{23}-R_{15}),T(R_{13}-R_{45}),T(R_{35}-R_{12})$, respectively. For any $T$ supported away from the six template wires, the result is $4T(R_{12}R_{34}-R_{34}R_{56})$. This is the recursive first-bracket substitution and carries no complexity bound.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 35, Recursive explicit lift of all disjoint exchange-monomial Hamiltonians

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P49

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

attribute [local instance 100] LieRing.ofAssociativeRing

-- Specialize the frozen generic aliases without declaring new aliases.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "Vec" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Vec (Qubits n))

-- The frozen support predicate takes the support before the operator.

local notation "WireSupported" => QAlgorithms.Papers.Independent.Information100.P69.Supported

/-- PDF pp.33–35, I25–I37: the explicit monomial lift, finite Lie expressions,
the recursive Q-lift, and the actual first-bracket substitution of I35/I36. -/
theorem recursive_monomial_lift (n : ℕ) :
    (∀ h : (l : ℕ) → (Fin l ↪ Fin n) → ℝ,
      (liftMonomialHamiltonian n h).IsHermitian ∧
      (∃ e : ExchangeExpr (n+2), e.eval = Complex.I • liftMonomialHamiltonian n h) ∧
      ∀ psi : Vec n, act (liftMonomialHamiltonian n h) (tensorState psi (zeroKet 2)) =
        tensorState (act (monomialHamiltonian n h) psi) (zeroKet 2)) ∧
    (∀ l : ℕ, Even l → 4 ≤ l → l ≤ n →
      (∃ e : ExchangeExpr (n+2), e.eval = Complex.I •
        (registerTensor (standardQ n l) (1 : Op 2) -
          registerTensor (standardQ n (l-2)) (heisenbergExchange (0 : Fin 2) 1))) ∧
      liftQ n l = registerTensor (standardQ n l) (1 : Op 2) -
        registerTensor (standardQ n (l-2)) (heisenbergExchange (0 : Fin 2) 1) + (1/2 : ℂ) • liftQ n (l-2)) ∧
    (∀ (N : ℕ) (w : Fin 6 ↪ Fin N) (T : Op N) (s : Finset (Fin N)),
      WireSupported s T → (∀ q : Fin 6, w q ∉ s) →
      commutatorTemplate w (fun a => T*(templateSeeds w a-templateComplements w a)) =
        (4 : ℂ) • (T*(heisenbergExchange (w 0) (w 1)*heisenbergExchange (w 2) (w 3) -
          heisenbergExchange (w 2) (w 3)*heisenbergExchange (w 4) (w 5)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
