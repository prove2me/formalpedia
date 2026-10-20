-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_nearby_private_bit_corner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.nearby_private_bit_corner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:16:50.259535+00:00
-- url     : https://prove2.me/theorems/ca27d3b5-9655-49eb-9c34-5cb247b3035e
-- title:
--   Proposition 3: nearby private bit implies large corner block
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $\rho$ be a state with two-qubit key, $\gamma$ a private bit in the same fixed key basis, and $0<\epsilon<1$. If $\|\rho-\gamma\|_1\le\epsilon$, then
--
--   $$\|\langle00|\rho|11\rangle\|_1\ge\tfrac12-\epsilon.$$
--
--   Thus proximity to a private bit forces a large corner block in its key basis.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 13, Proposition 3: nearby private bit implies large corner block

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.13, Proposition 3: same key basis. Eq.(68)'s 1-epsilon is a typo;
the proposition and the immediately preceding line say 1/2-epsilon. -/
theorem nearby_private_bit_corner {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (rho gamma : Op (Key 2 × (S × T)))
    (hrho : IsDensityMatrix rho) (hgamma : IsPrivate gamma)
    (eps : ℝ) (hpos : 0 < eps) (hlt : eps < 1) (hclose : traceNorm (rho-gamma) ≤ eps) :
    traceNorm (keyBlock rho (0,0) (1,1)) ≥ 1/2-eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
