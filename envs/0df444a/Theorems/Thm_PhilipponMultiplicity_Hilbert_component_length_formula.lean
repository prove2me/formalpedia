-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
-- name    : PhilipponMultiplicity.Hilbert.component_length_formula
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-26T23:12:04.365993+00:00
-- url     : https://prove2.me/theorems/b47c1041-c482-428c-a8fe-e4a82f607129
-- title:
--   Component-length formula over any field and at every natural degree
-- statement:
--   For every multihomogeneous ideal $I$ in a multiprojective coordinate ring over any field, and every natural multidegree $d$, its normalized top Hilbert-degree form satisfies
--   $$H(I;d)=\sum_{q} \operatorname{length}_{R_q}(R_q/IR_q)\,H(q;d),$$
--   where the sum runs over the relevant minimal primes of $I$ having the same Hilbert dimension as $I$. The length is the actual finite localized module length. This is the field-general, zero-entry-inclusive associativity formula underlying Philippon's Lemma 3.2. The original numbered lemma remains unchanged.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Lemma 3.2, printed p. 364. This general interface exposes the already completed homogeneous-prime-filtration proof for every field and all natural evaluation degrees; the numbered source target is unchanged. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.component_length_formula
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d : M.FactorIndex → ℕ) :
    idealDegreeValue M I d = topComponentLengthSum M I d := by sorry
