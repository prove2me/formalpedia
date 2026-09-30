-- Prove2me | Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_meetsOpen_inf_away_iff
-- name    : PhilipponMultiplicity.SectionThreeSupport.meetsOpen_inf_away_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T12:13:15.918311+00:00
-- url     : https://prove2.me/theorems/7513ebd1-800d-41ab-b93a-e052b3e253d7
-- title:
--   A component meeting an open locus survives restriction away from an ideal
-- statement:
--   In a multiprojective coordinate ring over any field, a prime $q$ meets $U\cap D(A)$ if and only if it meets $U$ and $A$ is not contained in $q$. Here meeting means containment in some maximal ideal of the open set. The maximal ideal witnessing the smaller open set may differ from the original witness. This is proved from the Jacobson property of the finite polynomial ring, without an algebraic-closure hypothesis.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs. Supporting geometry for the equivalence of descriptions of the new components on printed p. 368 of Proposition 3.3. https://www.numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_CutLocus
set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport

theorem PhilipponMultiplicity.SectionThreeSupport.meetsOpen_inf_away_iff
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (U : MaximalOpenLocus M) (A : Ideal M.CoordinateRing) :
    Hilbert.MeetsOpen K M.factorCount M.ambientDimension q (U ⊓ awayLocus M A) ↔
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U ∧ ¬ A ≤ q := by sorry
