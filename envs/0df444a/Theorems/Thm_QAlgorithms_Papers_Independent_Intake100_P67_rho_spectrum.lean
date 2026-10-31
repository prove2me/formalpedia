-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_rho_spectrum
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.rho_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:22:31.474405+00:00
-- url     : https://prove2.me/theorems/822fd14e-e5ea-4314-8e5d-74b79820ed4d
-- title:
--   Complete coupled-spin spectrum and multiplicities of rho
-- statement:
--   Let $N\ge1$ and $\rho=\sum_i2^{-(N-1)}P^-_{A_iC}\otimes I_{\bar A_i}$. The legal doubled Alice spins are integers $k\in\{0,\ldots,N\}$ with $k\equiv N\pmod2$; write $j=k/2$. Let $P_j$ be the spin-$j$ projector on Alice's $N$ qubits. Let $Q_j^-$ and $Q_j^+$ be the joint projectors onto Alice spin $j$ and total $AC$ spins $j+1/2$ and $j-1/2$, respectively; $Q_0^+=0$. Define
--
--   $$g_N(j)=\frac{(2j+1)N!}{(N/2-j)!(N/2+j+1)!},\quad \lambda_j^-=\frac{N/2-j}{2^N},\quad\lambda_j^+=\frac{N/2+j+1}{2^N}.$$
--
--   These are Hermitian idempotent sector projectors, with $\operatorname{tr}Q_j^-=(2j+2)g_N(j)$ and $\operatorname{tr}Q_j^+=2jg_N(j)$, and
--
--   $$\sum_j(Q_j^-+Q_j^+)=I,\qquad \rho=\sum_j(\lambda_j^-Q_j^-+\lambda_j^+Q_j^+),\qquad \rho Q_j^\pm=\lambda_j^\pm Q_j^\pm.$$
--
--   Every vector in either projector range obeys the corresponding eigenvalue equation. These ranges are precisely the coupled-spin eigenspaces in (8), simultaneously covering all magnetic and multiplicity labels.
--
--   This describes the full spectrum, including its zero eigenspace.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 3, §III, Eqs. (7)–(23); Appendix A p.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.3–5, Eqs.(7)–(23), Appendix A p.11: full spectral decomposition, eigenstates
as ranges of the coupled-spin projectors of Eq.(8), and their degeneracies.
A basis-independent projector describes all m and multiplicity labels at once. -/
theorem rho_spectrum (N : ℕ) (hN : 1 ≤ N) :
    portRho N = ∑ k ∈ spins N,
      ((lambdaMinus N k : ℂ) • minusSector N k + (lambdaPlus N k : ℂ) • plusSector N k) ∧
    (∑ k ∈ spins N, (minusSector N k + plusSector N k)) = 1 ∧
    (∀ k ∈ spins N,
      (minusSector N k).IsHermitian ∧ (plusSector N k).IsHermitian ∧
      minusSector N k * minusSector N k = minusSector N k ∧
      plusSector N k * plusSector N k = plusSector N k ∧
      (minusSector N k).trace.re = ((k + 2) * spinMultiplicity N k : ℕ) ∧
      (plusSector N k).trace.re = (k * spinMultiplicity N k : ℕ) ∧
      portRho N * minusSector N k = (lambdaMinus N k : ℂ) • minusSector N k ∧
      portRho N * plusSector N k = (lambdaPlus N k : ℂ) • plusSector N k ∧
      (∀ v : EuclideanSpace ℂ (AC N), act (minusSector N k) v = v →
        act (portRho N) v = (lambdaMinus N k : ℂ) • v) ∧
      (∀ v : EuclideanSpace ℂ (AC N), act (plusSector N k) v = v →
        act (portRho N) v = (lambdaPlus N k : ℂ) • v)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
