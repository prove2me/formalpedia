-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_oddJointMoments
-- name    : QAlgorithms.Papers.Independent.Information100.P22.oddJointMoments
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:06:15.150906+00:00
-- url     : https://prove2.me/theorems/d89d30f7-b60d-4268-8ec1-27452a3cd634
-- title:
--   §II B / S1.3, unnumbered: guaranteed odd-m joint-signal moments
-- statement:
--   Let $m,k\ge1$ with $m$ odd, choose ordered distinct axes, any normalized pure resource, and $c\in\{0,1\}^k$. Put $R_0=iPQ$, $\sigma_m=(-1)^{(m-1)/2}$, $R_A(c)=\bigotimes_jR_0^{c_j}$ and $T(c)=\bigotimes_{j,i}R_0^{c_j}$. Then
--   $$U^\dagger(I\otimes T(c))U=\sigma_m^{|c|}R_A(c)\otimes I,\qquad\operatorname{Tr}[T(c)C_S(\rho)]=\sigma_m^{|c|}\operatorname{Tr}[R_A(c)\rho].$$
--   The second equality holds for every input density operator. These moments determine its product-$R_0$-basis diagonal statistics. They need not exhaust the joint information. Both $m=1$ and $c=0$ are included.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 4, §II B / S1.3, unnumbered: guaranteed odd-m joint-signal moments

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Eqs.(S12)–(S13), PDF pp.23–24 and main p.4. Includes c=0 and m=1. -/
theorem oddJointMoments (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hodd : Odd m)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) (c : Qubits k) :
    (twoPauliEncoder m k P Q)ᴴ * Matrix.kronecker (1 : Op (Qubits k)) (sectorMoment m k P Q c) *
      twoPauliEncoder m k P Q = ((-1 : ℂ)^((m-1)/2))^(hammingWeight c) •
        Matrix.kronecker (inputMoment k P Q c) (1 : Op (Signals m k)) ∧
    ∀ rho : Op (Qubits k), IsDensityMatrix rho →
      (sectorMoment m k P Q c * jointSignals R (twoPauliEncoder m k P Q) rho).trace =
        ((-1 : ℂ)^((m-1)/2))^(hammingWeight c) * (inputMoment k P Q c * rho).trace := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
