-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_multi_swap_nonlocal
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.multi_swap_nonlocal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:14:40.942135+00:00
-- url     : https://prove2.me/theorems/8e64b15f-935e-4e3d-a5b9-404fc51f14da
-- title:
--   Multi-qubit swap has positive overlap with every C_l and is nonlocal
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $n=2r\ge2$ and let $S=P_{12}P_{34}\cdots P_{n-1,n}$ exchange the odd and even $r$-qubit registers. For every even $0\le l\le n$,
--   $$\operatorname{Tr}(SC_l)=2^{(l-n)/2}\frac{(n-l)!(n/2)!}{n!((n-l)/2)!}\operatorname{Tr}(C_l^2)>0.$$
--   For every $k<n$, the entire family $e^{-itS}$ cannot belong to $\mathcal V_k$ for all real $t$. For $2\le k<n$, only finitely many $\phi\in[0,2\pi)$ have $e^{i\phi S}\in\mathcal V_k$. Exceptional nonzero endpoint phases are allowed; the claim does not exclude every nonzero $\phi$.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 29, Multi-qubit swap has positive overlap with every C_l and is nonlocal

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

/-- PDF pp.4–5,29, H4: positive overlap at every physical even weight, and
nonlocality of the full Hamiltonian evolution. Exceptional endpoint phases are retained. -/
theorem multi_swap_nonlocal (r : ℕ) (hr : 0<r) :
    (∀ l : ℕ, Even l → l ≤ 2*r →
      Matrix.trace (multiSwap r * central (2*r) l) =
        (permutationSumCoefficient (2*r) (2*r) l * (Nat.factorial r : ℝ) : ℂ) *
          Matrix.trace (central (2*r) l ^ 2) / (Nat.factorial (2*r) : ℂ) ∧
      0 < (Matrix.trace (multiSwap r * central (2*r) l)).re) ∧
    (∀ k : ℕ, k<2*r → ¬(∀ t : ℝ, evolve (multiSwap r) t ∈ localGroup (2*r) k)) ∧
    (∀ k : ℕ, 2 ≤ k → k<2*r →
      {phi : ℝ | 0 ≤ phi ∧ phi<2*Real.pi ∧
        evolve (multiSwap r) (-phi) ∈ localGroup (2*r) k}.Finite) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
