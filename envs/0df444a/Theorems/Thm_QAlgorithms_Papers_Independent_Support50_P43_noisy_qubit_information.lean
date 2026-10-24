-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_noisy_qubit_information
-- name    : QAlgorithms.Papers.Independent.Support50.P43.noisy_qubit_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:35:26.520987+00:00
-- url     : https://prove2.me/theorems/1752635b-0b94-4b65-ac06-a597a6c77874
-- title:
--   Figure 2(a,b): noisy GHZ/W information comparisons
-- statement:
--   Let $\psi$ be either the three-qubit GHZ vector $(|000\rangle+|111\rangle)/\sqrt2$ or the W vector $(|001\rangle+|010\rangle+|100\rangle)/\sqrt3$. For $0\le p\le1$, put $\rho_p=p|\psi\rangle\langle\psi|+(1-p)\mathbf1_8/8$. Define $I= S(AB)+S(AC)+S(BC)-2S(ABC)$, $I_x=S(A)+S(B)+S(C)-S(ABC)$, and $I_c=S(A)+S(B)+S(C)-S(AB)-S(AC)-S(BC)+S(ABC)$, evaluated on $\rho_p$ in bits. Let $E_N(A:BC)=\log_2\|\rho_p^{T_A}\|_1$, where $T_A$ is computational partial transpose and $\|\cdot\|_1$ is the full trace norm. Then
--   $$
--   \begin{gathered}
--   I_c(\rho_0)=I_c(\rho_1)=0,\qquad 0<p<1\Longrightarrow I_c(\rho_p)<0,\\
--   I(\rho_p)=0\Longleftrightarrow p=0,\qquad p>0\Longrightarrow I(\rho_p)>0,\\
--   I_x(\rho_p)\le I(\rho_p),\qquad I_c(\rho_p)\le E_N(A:BC)_{\rho_p},\\
--   p>0\Longrightarrow I_c(\rho_p)<E_N(A:BC)_{\rho_p}.
--   \end{gathered}
--   $$
--
--   These are comparisons for the two displayed families, not for arbitrary mixed states.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 4, Figure 2(a,b) caption

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Figure 2(a,b), PDF p.4: every caption comparison on exactly the two qubit
families, including strict negativity-versus-common-information comparison for p>0.
At p=0 the comparison is non-strict. Panel (c) is deferred. -/
theorem noisy_qubit_information (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ psi : EuclideanSpace ℂ (HomBasis 3 2), psi = ghzKet 3 true ∨ psi = dickeQubitVector 3 1 →
    let rho := noisyQubits psi p
    ((p = 0 ∨ p = 1) → commonOn rho Finset.univ = 0) ∧
    ((0 < p ∧ p < 1) → commonOn rho Finset.univ < 0) ∧
    (alternativeOn rho Finset.univ = 0 ↔ p = 0) ∧
    (0 < p → 0 < alternativeOn rho Finset.univ) ∧
    conventionalOn rho Finset.univ ≤ alternativeOn rho Finset.univ ∧
    commonOn rho Finset.univ ≤ logarithmicNegativity rho ∧
    (0 < p → commonOn rho Finset.univ < logarithmicNegativity rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
