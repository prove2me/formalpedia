-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_cat_photonImbalance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.cat_photonImbalance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:28:27.906323+00:00
-- url     : https://prove2.me/theorems/4bdbc3dd-5dda-4a3f-9ac5-73bca52b25a2
-- title:
--   Exact cat photon-number imbalance
-- statement:
--   Let $a>0$ be real and $S\ge0$ an integer. For the normalized projected-coherent cat states $|\mu_a\rangle$, define $N_a^r=\langle a|\Pi_r|a\rangle$ with residue $r$ taken modulo $2(S+1)$. Their first photon-number moments are finite, and their half-difference is
--
--   $$\delta\bar n=\frac{\langle0_a|\hat n|0_a\rangle-\langle1_a|\hat n|1_a\rangle}{2}=\frac{a^2}{2}\left(\frac{N_a^{-1}}{N_a^0}-\frac{N_a^S}{N_a^{S+1}}\right).$$
--
--   This is an exact identity. Interpreting no loss as the dominant event requires a separate small-$\gamma\bar n$ regime and is not a hypothesis of this formula.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 11, §V B (5.14): cat photon-number imbalance

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.11 (5.14): exact photon-number imbalance, without a small-loss hypothesis. -/
theorem cat_photonImbalance (a : ℝ) (ha : 0 < a) (S : ℕ) :
    (∀ mu : Fin 2, fockMomentDomain (catCodeCoordinates a S mu) 1) ∧
    (numberMoment (catCodeCoordinates a S 0) 1 - numberMoment (catCodeCoordinates a S 1) 1) / 2 =
      a ^ 2 / 2 * (catNorm a S (-1) / catNorm a S 0 -
        catNorm a S S / catNorm a S (S + 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
