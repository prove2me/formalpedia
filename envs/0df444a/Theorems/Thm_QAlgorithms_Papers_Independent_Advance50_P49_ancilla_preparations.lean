-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_ancilla_preparations
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.ancilla_preparations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:16:23.723278+00:00
-- url     : https://prove2.me/theorems/0d43343d-41cb-4e2c-9459-18d615adcea6
-- title:
--   Two-ancilla universality for triplet and singlet preparations
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For every invariant target unitary $V$, a single finite exchange circuit $W$ on the $n+2$ chain works for every data density matrix $\rho$ and every ancillary density matrix $\tau$ supported in the triplet:
--   $$W(\rho\otimes\tau)W^{\dagger}=(V\rho V^{\dagger})\otimes\tau.$$
--   There is also an exchange circuit with the same property for $\tau=|\xi\rangle\langle\xi|$, $|\xi\rangle=(|01\rangle-|10\rangle)/\sqrt2$. Both witnesses precede the data, and the triplet witness also precedes $\tau$. At the elementary step, for invariant Hermitian $F$ supported away from distinct wires $a,b$,
--   $$K=FR_{ab}\otimes I-F\otimes R_{\mathrm{anc}}$$
--   is exchange-Lie reachable and acts as $FR_{ab}-F/2$ on triplet inputs and $FR_{ab}+3F/2$ on singlet inputs. The action identities hold for all vectors. This permits symmetric mixed ancillary preparation as well as the pure zero preparation.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 4, Two-ancilla universality for triplet and singlet preparations

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

/-- PDF pp.4,31–33: two ancillary preparation regimes, uniformly over all triplet
states. The singlet is corrected using p.31. PSD and trace-one are explicit. -/
theorem ancilla_preparations (n : ℕ) (V : Op n) (hV : SymUnitary V) :
    (∃ W : Op (n+2), W ∈ exchangeGroup (n+2) true false ∧
      ∀ (rho : Op n) (tau : Op 2), IsDensityMatrix rho → IsDensityMatrix tau →
        triplet*tau*triplet=tau →
        W*registerTensor rho tau*Wᴴ = registerTensor (V*rho*Vᴴ) tau) ∧
    (∃ W : Op (n+2), W ∈ exchangeGroup (n+2) true false ∧
      ∀ rho : Op n, IsDensityMatrix rho →
        W*registerTensor rho (pureDensity twoQubitSinglet)*Wᴴ = registerTensor (V*rho*Vᴴ) (pureDensity twoQubitSinglet)) ∧
    (∀ (F : Op n) (a b : Fin n) (s : Finset (Fin n)),
      F.IsHermitian → RotationInvariant F → WireSupported s F → a∉s → b∉s → a≠b →
      let K := registerTensor (F*heisenbergExchange a b) (1 : Op 2) - registerTensor F (heisenbergExchange (0 : Fin 2) 1)
      Complex.I • K ∈ exchangeLie (n+2) false false ∧
      (∀ (psi : Vec n) (eta : Vec 2), act triplet eta=eta →
        act K (tensorState psi eta) =
          tensorState (act (F*heisenbergExchange a b-(1/2 : ℂ) • F) psi) eta) ∧
      (∀ psi : Vec n, act K (tensorState psi twoQubitSinglet) =
        tensorState (act (F*heisenbergExchange a b+(3/2 : ℂ) • F) psi) twoQubitSinglet)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
