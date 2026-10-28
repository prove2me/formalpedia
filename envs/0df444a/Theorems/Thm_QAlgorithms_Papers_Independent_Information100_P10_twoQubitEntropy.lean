-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_twoQubitEntropy
-- name    : QAlgorithms.Papers.Independent.Information100.P10.twoQubitEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:39:54.826643+00:00
-- url     : https://prove2.me/theorems/b969ea7d-b7b2-4f83-9a70-dec91c7620d9
-- title:
--   Two-qubit entropy as an explicit monotone function of ED, Eqs.(40)–(41)
-- statement:
--   Let $\psi$ be a normalized pure two-qubit state, let $\rho_A=\operatorname{Tr}_B|\psi\rangle\langle\psi|$, and let $k_B>0$. Define $S(\psi)=-k_B\operatorname{Tr}(\rho_A\ln\rho_A)$ with $0\ln0=0$, and put $F(x)=-x\ln x-(1-x)\ln(1-x)$. The reduced matrix is a density matrix, $E(\psi)\in[0,2]$, and
--
--   $$S(\psi)=k_B F\left(\frac{1+\sqrt{1-E(\psi)/2}}{2}\right).$$
--
--   The function of ED on the right is strictly increasing on $[0,2]$. This expresses the entropy, defined from the actual reduced density, in terms of ED. The library entropy in bits is multiplied by $k_B\ln2$ to obtain these natural-log units.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 5, Two-qubit entropy as an explicit monotone function of ED, Eqs.(40)–(41)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.5, Eqs.(40)-(41): entropy computed from the reduced density is the explicit
strictly increasing function of ED; kB is the positive Boltzmann scale. -/
theorem twoQubitEntropy (psi : Ket 2) (hpsi : IsState psi)
    (kB : ℝ) (hkB : 0 < kB) :
    IsDensityMatrix (reducedFirst psi) ∧
    entanglementDistance psi ∈ Set.Icc (0 : ℝ) 2 ∧
    entropyOfEntanglement kB psi = entropyProfile kB (entanglementDistance psi) ∧
    StrictMonoOn (entropyProfile kB) (Set.Icc 0 2) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
