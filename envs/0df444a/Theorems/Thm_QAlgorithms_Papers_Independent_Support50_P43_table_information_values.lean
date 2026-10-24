-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_table_information_values
-- name    : QAlgorithms.Papers.Independent.Support50.P43.table_information_values
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:34:35.563554+00:00
-- url     : https://prove2.me/theorems/0487a9c3-54d9-45b4-b51d-8e571b07863e
-- title:
--   Table I: eight exact information pairs
-- statement:
--   For a pure finite multipartite state $\rho=|\psi\rangle\langle\psi|$, define $I(\rho)=\sum_i S(\bar i)-(n-1)S([n])$ and common information $I_c(\rho)=\sum_{\varnothing\ne T\subseteq[n]}(-1)^{|T|+1}S(T)$, with entropy in bits. Write $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$, with $0\log_20=0$.
--
--   Here $|\mathrm{GHZ}_n\rangle=(|0^n\rangle+|1^n\rangle)/\sqrt2$, and $|D_n^r\rangle$ is the equal superposition of the distinct weight-$r$ strings divided by $\sqrt{\binom nr}$. The three-qutrit vector is $|\psi_{\mathrm{as}}\rangle=(|123\rangle-|132\rangle+|231\rangle-|213\rangle+|312\rangle-|321\rangle)/\sqrt6$. Finally, $|C_4\rangle=(|0000\rangle+|0011\rangle+|1100\rangle-|1111\rangle)/2$. The exact pairs are
--   $$
--   \begin{aligned}
--   (I_c,I)(\mathrm{GHZ}_2)&=(2,2),&
--   (I_c,I)(\mathrm{GHZ}_3)&=(0,3),\\
--   (I_c,I)(D_3^1)&=(0,3h_2(1/3)),&
--   (I_c,I)(\psi_{\mathrm{as}})&=(0,3\log_2 3),\\
--   (I_c,I)(\mathrm{GHZ}_4)&=(2,4),&
--   (I_c,I)(D_4^1)&=(8h_2(1/4)-6,4h_2(1/4)),\\
--   (I_c,I)(D_4^2)&=(8h_2(1/4)-6,4),&
--   (I_c,I)(C_4)&=(-2,4).
--   \end{aligned}
--   $$
--
--   These reproduce the displayed rounded decimals while distinguishing the nonnegative alternative information from signed common information.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 5, Table I (announced on PDF p.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- Table I, PDF p.5 (announced on p.3), all eight rows. Decimal displays are
replaced by their exact entropy expressions, not exact decimal equalities. -/
theorem table_information_values :
    informationPair (ghzKet 2 true) = (2,2) ∧
    informationPair (ghzKet 3 true) = (0,3) ∧
    informationPair (dickeQubitVector 3 1) = (0,3 * binEntropy2 (1/3)) ∧
    informationPair antisymmetric = (0,3 * Real.logb 2 3) ∧
    informationPair (ghzKet 4 true) = (2,4) ∧
    informationPair (dickeQubitVector 4 1) = (8 * binEntropy2 (1/4) - 6,4 * binEntropy2 (1/4)) ∧
    informationPair (dickeQubitVector 4 2) = (8 * binEntropy2 (1/4) - 6,4) ∧
    informationPair cluster = (-2,4) := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
