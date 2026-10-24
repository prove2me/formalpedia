-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_cloner12_degradable
-- name    : QAlgorithms.Papers.Independent.Support50.P01.cloner12_degradable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:12:33.244926+00:00
-- url     : https://prove2.me/theorems/1931526d-87f0-4fc2-befe-f00c1d803499
-- title:
--   §III.A: the 1→2 universal cloner is also degradable
-- statement:
--   Let $1\le N\le M$ be integers. Let $\mathrm{Cl}_{N,M}$ be the specified optimal universal qubit cloner on $\operatorname{Sym}^N(\mathbb C^2)$, with receiver support $\operatorname{Sym}^M(\mathbb C^2)$ and environment dimension $M-N+1$. Its common dilation on normalized occupation kets is exactly Eqs.(21),(22). Write $\pi_d=I_d/d$, $I_c$ for coherent information in bits, $Q^{(1)}$ for its supremum over all density inputs, and $Q$ for its regularization over all positive block lengths and arbitrary entangled block inputs. In the $1\to2$ case there are input-independent CPTP maps $D$ and $D_c$ on the entire three-dimensional receiver support such that
--   $$
--   D\circ\mathrm{Cl}_{1,2}=\mathrm{Cl}_{1,2}^c,\qquad D_c\circ\mathrm{Cl}_{1,2}=T\circ\mathrm{Cl}_{1,2}^c.
--   $$
--   Thus the specified cloner is both ordinarily and conjugately degradable. Compression to the symmetric support avoids treating a non-trace-preserving projection on the full two-qubit space as a channel.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 6, §III.A: the 1→2 universal cloner is also degradable

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

/-- PDF p.6: ordinary and conjugate degradability, on the compressed symmetric receiver.
The CPTP witness is trace preserving on its entire three-dimensional domain. -/
theorem cloner12_degradable :
    IsDegradable (clonerDilation 1 2) ∧ ConjugateDegradable (clonerDilation 1 2) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
