-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_large_corner_near_private_bit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.large_corner_near_private_bit
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T16:17:33.83489+00:00
-- url     : https://prove2.me/theorems/a474d1be-ee1d-4fcf-a521-4ae0ec2f0b26
-- title:
--   Proposition 4: large corner block implies nearby private bit
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $\rho$ have a two-qubit key and $0<\epsilon<1/8$. If $\|\langle00|\rho|11\rangle\|_1>1/2-\epsilon$, there is a private bit $\gamma$ on the same registers such that
--
--   $$\|\rho-\gamma\|_1\le\delta(\epsilon),\quad\delta(\epsilon)=2\sqrt{8\sqrt{2\epsilon}+h_2(2\sqrt{2\epsilon})}+2\sqrt{2\epsilon}.$$
--
--   Here $h_2(x)=-x\log_2x-(1-x)\log_2(1-x)$, with $0\log 0=0$. Moreover $\lim_{\epsilon\downarrow0}\delta(\epsilon)=0$. The bound is independent of both shield dimensions and makes a large corner block a criterion for approximation by private bits.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 13, Proposition 4: large corner block implies nearby private bit

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

/-- PDF pp.13–14, Proposition 4, Eq.(70): explicit error and its right-hand limit. -/
theorem large_corner_near_private_bit :
    Filter.Tendsto privateBitError (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    ∀ {S T : Type} [Fintype S] [Fintype T] [Nonempty S] [Nonempty T]
      (rho : Op (Key 2 × (S × T))), IsDensityMatrix rho →
      ∀ eps : ℝ, 0 < eps → eps < 1/8 → traceNorm (keyBlock rho (0,0) (1,1)) > 1/2-eps →
      ∃ gamma : Op (Key 2 × (S × T)), IsPrivate gamma ∧ traceNorm (rho-gamma) ≤ privateBitError eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
