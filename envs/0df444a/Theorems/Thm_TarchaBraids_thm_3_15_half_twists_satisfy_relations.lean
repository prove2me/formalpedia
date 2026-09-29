-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_half_twists_satisfy_relations
-- name    : TarchaBraids.thm_3_15_half_twists_satisfy_relations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T23:38:08.740031+00:00
-- url     : https://prove2.me/theorems/3003b2e4-9cdb-45d6-9ee7-310d162fff72
-- title:
--   Teorema 3.15 (homomorphism step): the half-twists satisfy Artin's relations
-- statement:
--   The first half of the proof of Tarcha's Teorema 3.15 checks that the assignment
--   $x_i \mapsto [\sigma_i]$ respects the defining relations, so that it extends to a group
--   homomorphism from the abstractly presented group to the braid group. Geometrically this is exactly
--   the pair of relations of Proposição 3.14 and of the discussion following it, verified for the
--   half-twist loops themselves:
--   $$[\mathrm{ht}_i]\,[\mathrm{ht}_j] = [\mathrm{ht}_j]\,[\mathrm{ht}_i] \qquad (|i-j| \ge 2),$$
--   $$[\mathrm{ht}_i]\,[\mathrm{ht}_{i+1}]\,[\mathrm{ht}_i]
--    = [\mathrm{ht}_{i+1}]\,[\mathrm{ht}_i]\,[\mathrm{ht}_{i+1}].$$
--   The first relation holds because half-twists with non-adjacent indices are supported in disjoint
--   discs; the second is the braid relation, whose proof in the dissertation is the isotopy displayed in
--   Figura 3.17 and its generalization.
-- source:
--   Alexsander Andrey Gomes Tarcha, *Um Estudo Introdutório da Teoria de Tranças*, Dissertação (Mestrado Profissional em Matemática), IGCE, UNESP, Rio Claro, 2023, orientadora Alice Kimie Miwa Libardi, Proposição 3.14 e comentários seguintes, pp. 56–57 (relação de trança e relação de comutação), usados na demonstração do Teorema 3.15, pp. 57–58

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_half_twists_satisfy_relations (n : ℕ) :
    (∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs →
        halfTwistBraid n i * halfTwistBraid n j = halfTwistBraid n j * halfTwistBraid n i) ∧
    (∀ i j : Fin (n - 1), (j : ℕ) = (i : ℕ) + 1 →
        halfTwistBraid n i * halfTwistBraid n j * halfTwistBraid n i =
          halfTwistBraid n j * halfTwistBraid n i * halfTwistBraid n j) := by sorry

end TarchaBraids
