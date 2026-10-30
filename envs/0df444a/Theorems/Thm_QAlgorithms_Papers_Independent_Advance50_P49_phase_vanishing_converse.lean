-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_vanishing_converse
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_vanishing_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:13:43.805995+00:00
-- url     : https://prove2.me/theorems/14e45d7a-feb4-4622-87f1-0298e8800a61
-- title:
--   Corollary 1: phase-vanishing converse modulo a fixed finite group
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $k\ge2$ and let $V$ be invariant and unitary with $\Phi_l(V)=0$ for every even $l>k$. For the fixed finite subgroup $G_0$ just defined,
--   $$\exists V_0\in G_0:\quad V_0^{\dagger}V\in\mathcal V_k.$$
--   Thus the necessary phase constraints become sufficient up to a fixed finite ambiguity. The condition $k\ge2$, omitted in the printed corollary, is inherited from its use of the $S\mathcal V_2$ factor and is necessary.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 26, Corollary 1: phase-vanishing converse modulo a fixed finite group

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

/-- PDF p.26, Corollary 1. The necessary k≥2 is inherited from Theorem 2;
the printed corollary omits it. -/
theorem phase_vanishing_converse (n k : ℕ) (hk : 2 ≤ k) (V : Op n)
    (hV : SymUnitary V) (hPhase : ∀ l : ℕ, Even l → k<l → bodyPhase V l=0) :
    ∃ Vzero : Op n, Vzero ∈ finitePhaseGroup n ∧ Vzeroᴴ*V ∈ localGroup n k := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
