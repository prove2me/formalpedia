-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloner_singleUse_asymptotics
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloner_singleUse_asymptotics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:18:47.199294+00:00
-- url     : https://prove2.me/theorems/ef540e96-e934-42fe-8376-cc9fe836b1b2
-- title:
--   §III.C: coherent information tends to zero with diverging M/N
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. For each fixed $N\ge1$, $M\mapsto Q^{(1)}(\mathrm{Cl}_{N,M})$ is nonincreasing on integers $M\ge N$. If integer sequences obey $1\le N_t\le M_t$ and $M_t/N_t\to+\infty$, then
--   $$\lim_{t\to\infty}Q^{(1)}(\mathrm{Cl}_{N_t,M_t})=0.$$
--   This is a limit of maximized single-use information, not an unproved limit for general regularized capacities.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 11, §III.C: coherent information tends to zero with diverging M/N

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

/-- PDF p.11: fixed-N monotonicity and the divergent-ratio limit concern optimized
single-use information, not the unknown general regularized capacity. -/
theorem cloner_singleUse_asymptotics :
    (∀ N : ℕ, 1≤N → AntitoneOn (fun M => maximumCoherentInformation (clonerDilation N M))
      {M : ℕ | N≤M}) ∧
    (∀ N M : ℕ → ℕ, (∀ t, 1≤N t ∧ N t≤M t) →
      Tendsto (fun t => (M t : ℝ)/(N t : ℝ)) atTop atTop →
      Tendsto (fun t => maximumCoherentInformation (clonerDilation (N t) (M t))) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
