-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_invariant_volume_law
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.invariant_volume_law
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:16:50.333713+00:00
-- url     : https://prove2.me/theorems/b16ee86e-2eb6-4a64-82f2-0514bf0f9960
-- title:
--   Main properties (ii): one family has both exact translation invariance and volume-law entropy
-- statement:
--   For every integer $L\ge1$, there is a bond-one RAGE vector on $N=2L$ sites with normalized plus input, identity final rotations, and phase $\pi$ precisely on pairs of opposite sites of the cycle. Its symmetric graph weights lie in $[0,2\pi)$. The vector $\psi$ is normalized and exactly cyclically invariant. For every cyclically contiguous block $B$ of length $0\le\ell\le L$,
--
--   $$T\psi=\psi,\qquad S(\rho_B)=\ell\ \text{bits}.$$
--
--   Here $\rho_B$ is the actual reduced density matrix of $\psi$. This one explicit compatible family simultaneously realizes exact translation invariance and maximal volume-law block entropy, including wrapping blocks.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 2, Main properties (ii): one family has both exact translation invariance and volume-law entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF p.2, (i)–(ii): one family is simultaneously cyclically invariant and has maximal
volume-law entropy for every contiguous block of length at most half the chain. The compatible
circulant matching pins the source's existential claim; no external theorem is imported. -/
theorem invariant_volume_law (L : ℕ) (hL : 1 ≤ L) :
    ∃ G : PhaseGraph (2 * L), G.weight = oppositeWeights L ∧
      let v := rage (productTensors (plusFactors (2 * L))) G (fun _ => 1)
      IsState v ∧ CyclicInvariant v ∧
      (∀ (start : Fin (2 * L)) (ell : ℕ), ell ≤ L →
        IsDensityMatrix (rageMarginal v (cyclicBlock (2 * L) start ell)) ∧
        vnEntropy (rageMarginal v (cyclicBlock (2 * L) start ell)) = (ell : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
