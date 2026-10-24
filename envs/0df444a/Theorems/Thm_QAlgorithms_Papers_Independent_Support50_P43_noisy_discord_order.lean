-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P43_noisy_discord_order
-- name    : QAlgorithms.Papers.Independent.Support50.P43.noisy_discord_order
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:36:04.9934+00:00
-- url     : https://prove2.me/theorems/590ba6ae-1b76-4cf3-be53-1c6f0d6404e9
-- title:
--   Discord ordering for noisy GHZ and W families
-- statement:
--   Let $\rho_p=p|\psi\rangle\langle\psi|+(1-p)\mathbf1_8/8$ for $0\le p\le1$, where $\psi$ is the normalized three-qubit GHZ or W vector. For a set $M$ of measured parties, let $\Phi_{M,U}$ be nonselective dephasing in independently chosen local orthonormal bases $U$ on those parties, with identity on the others. For either $F=I$ or $F=I_x$, where $I=S(AB)+S(AC)+S(BC)-2S(ABC)$ and $I_x=S(A)+S(B)+S(C)-S(ABC)$ in bits, define
--   $$D_M^F(\rho)=F(\rho)-\max_U F(\Phi_{M,U}(\rho)).$$
--   Then both versions obey
--   $$D_A^F(\rho_p)\le D_{AB}^F(\rho_p)\le D_{ABC}^F(\rho_p).$$
--
--   The optimization uses independent local rank-one orthogonal projective measurements. This compares measurement on progressively more parties within the two specified state families.
-- source:
--   Multiparty Quantum Mutual Information: An alternative definition, arXiv:1504.07176v2, PDF p. 5, Unnumbered result following equations (16)–(18); Figure 3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P43

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- These accepted register types are definitionally the required finite tensor bases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet)

/-- PDF p.5, paragraph following (18), Figure 3: ordering of the alternative
and conventional discords for the displayed noisy GHZ and W families. -/
theorem noisy_discord_order (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ psi : EuclideanSpace ℂ (HomBasis 3 2), psi = ghzKet 3 true ∨ psi = dickeQubitVector 3 1 →
    ∀ alternative : Bool,
    let rho := noisyQubits psi p
    discord alternative {0} rho ≤ discord alternative {0,1} rho ∧
    discord alternative {0,1} rho ≤ discord alternative Finset.univ rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P43

end
