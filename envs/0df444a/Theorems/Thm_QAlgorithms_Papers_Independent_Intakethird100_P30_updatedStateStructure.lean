-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P30_updatedStateStructure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P30.updatedStateStructure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:37:49.178494+00:00
-- url     : https://prove2.me/theorems/0b24be22-093e-493a-98c9-083671f8eb21
-- title:
--   II A: matrix coefficients and block decomposition, (3)–(4)
-- statement:
--   Let $C=(C_k)_{k\in K}$ be a nonempty family of distinct $n$-bit words, $n\ge1$, and let $P_C(Q)$ be the Bob-only filtered six-state operator for $0\le Q\le\tfrac12$. For $a,a'\in\{0,1\}^n$, set $u=|a\oplus a'|$ and $v=|a\oplus C_k|$, where $|\cdot|$ counts ones. Call an entry compatible when $a\oplus C_k=a'\oplus C_l$ and $(a\oplus C_k)\mathbin{\odot}(a\oplus a')=0^n$, with $\odot$ bitwise AND. In that case $u+v\le n$, and
--
--   $$P_C(Q)_{a,k;a',l}=
--   \begin{cases}
--   ((1-2Q)/2)^u(Q/2)^v((1-Q)/2)^{n-u-v},&\text{compatible},\\
--   0,&\text{otherwise}.
--   \end{cases}$$
--
--   The fixed permutation $V|a,k\rangle=|a\oplus C_k,k\rangle$ is unitary and satisfies
--
--   $$VP_C(Q)V^\dagger=\bigoplus_{\beta\in\{0,1\}^n}M_\beta,
--   \qquad (M_\beta)_{kl}=P_C(Q)_{\beta\oplus C_k,k;\beta\oplus C_l,l}.$$
--
--   Both compatibility conditions are retained, so sector agreement alone is not asserted to make an entry nonzero.
-- source:
--   Numerical evidence for bound secrecy from two-way post-processing in quantum key distribution, arXiv:1612.07734v2, PDF p. 3, II A: matrix coefficients and block decomposition, (3)–(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P30

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J K L A B : Type}

variable [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [Fintype A] [Fintype B]

/-- PDF p.3, (3)–(4): both delta guards, compatible exponents, and actual unitary
block decomposition. No extra factor 2^(-n), and no erroneous nonzero iff. -/
theorem updatedStateStructure {n : ℕ} (hn : 1 ≤ n) [Nonempty K]
    (C : K → Qubits n) (hC : Function.Injective C) (Q : ℝ)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1 / 2) :
    (∀ (a a2 : Qubits n) (k l : K),
      (MatrixEntryCompatible C a a2 k l → hammingDist a a2 + hammingDist a (C k) ≤ n) ∧
      bobState C Q (a, k) (a2, l) =
        if MatrixEntryCompatible C a a2 k l then
          ((((1 - 2 * Q) / 2) ^ hammingDist a a2 *
            (Q / 2) ^ hammingDist a (C k) *
            ((1 - Q) / 2) ^ (n - hammingDist a a2 - hammingDist a (C k)) : ℝ) : ℂ)
        else 0) ∧
    (xorSectorPermutation C)ᴴ * xorSectorPermutation C = 1 ∧
    xorSectorPermutation C * (xorSectorPermutation C)ᴴ = 1 ∧
    (∀ p q, (xorSectorPermutation C * bobState C Q * (xorSectorPermutation C)ᴴ) p q =
      if p.1 = q.1 then xorSectorBlock C Q p.1 p.2 q.2 else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P30

end
