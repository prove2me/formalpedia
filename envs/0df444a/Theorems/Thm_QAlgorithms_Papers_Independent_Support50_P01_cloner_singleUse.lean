-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloner_singleUse
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloner_singleUse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:15:54.704657+00:00
-- url     : https://prove2.me/theorems/cacce1a7-beec-478f-9252-62fc4e15b95a
-- title:
--   §III.C, Eq.(30): optimized coherent information of all N→M cloners
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. For every such pair,
--   $$
--   \mathrm{Cl}_{N,M}(\pi_{N+1})=\pi_{M+1},\quad
--   \mathrm{Cl}_{N,M}^c(\pi_{N+1})=\pi_{M-N+1},\qquad
--   Q^{(1)}(\mathrm{Cl}_{N,M})=I_c(\mathrm{Cl}_{N,M},\pi_{N+1})
--   =\log_2(M+1)-\log_2(M-N+1)=\log_2\frac{M+1}{M-N+1}.
--   $$
--   The normalized maximally mixed input dominates every density input. This retains the all-$N,M$ single-use claim of Eq.(30), without asserting the general conjugate-degradability conjecture or an all-cloner exact capacity formula.
--
--   **Formalization Note** The printed Eqs.(23),(25),(29) omit the input factor $1/(N+1)$; the normalized output in this statement has unit trace. The source only supplies the concavity argument for its two established families, so the wider single-use claim has a disclosed proof gap.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 11, §III.C, Eq.(30): optimized coherent information of all N→M cloners

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF pp.10–11, Eq.(30): all-N,M SINGLE-USE optimized information.
The source supplies concavity only for its two proven families; its wider Eq.(30)
claim is retained without adding the general conjecture as a hypothesis.
Corrected normalization: the omitted 1/(N+1) in Eqs.(23),(25),(29) makes the
normalized environment output I/(M-N+1), not (N+1)I/(M-N+1). -/
theorem cloner_singleUse (N M : ℕ) (hN : 1≤N) (hNM : N≤M) :
    IsDensityMatrix (maximallyMixed (N+1)) ∧
    receiverChannel (clonerDilation N M) (maximallyMixed (N+1)) = maximallyMixed (M+1) ∧
    complementaryChannel (clonerDilation N M) (maximallyMixed (N+1)) = maximallyMixed (M-N+1) ∧
    coherentInformation (receiverChannel (clonerDilation N M)) (maximallyMixed (N+1)) =
      maximumCoherentInformation (clonerDilation N M) ∧
    maximumCoherentInformation (clonerDilation N M) = Real.logb 2 (M+1) - Real.logb 2 ((M-N+1 : ℕ) : ℝ) ∧
    maximumCoherentInformation (clonerDilation N M) = Real.logb 2 ((M+1 : ℝ) / (M-N+1 : ℕ)) ∧
    ∀ rho, IsDensityMatrix rho → coherentInformation (receiverChannel (clonerDilation N M)) rho ≤
      coherentInformation (receiverChannel (clonerDilation N M)) (maximallyMixed (N+1)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
