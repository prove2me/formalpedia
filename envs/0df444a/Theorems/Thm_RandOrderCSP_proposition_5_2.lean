-- Prove2me | Theorems.Thm_RandOrderCSP_proposition_5_2
-- name    : RandOrderCSP.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:16.134038+00:00
-- url     : https://prove2.me/theorems/2473611d-6743-4546-bf56-b41abf204624
-- title:
--   Proposition 5.2 — boundary support on a forest
-- statement:
--   Let $H$ be an acyclic $k$-uniform hypergraph and let $\Omega\in\mathbb Z_q^{\mathcal E_H\times[k]}$ be singleton-free, that is, $|\mathrm{supp}(\Omega_j)|\ne1$ for every edge $j$. Then $\mathrm{supp}(\partial_H\Omega)\in\mathrm{SF}_{\mathcal P_H}$, and if $\Omega\ne0$ then $\partial_H\Omega\ne0$.
--
--   The case $q=k=2$ is the handshaking lemma.
--
--   Differences from the source: none.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), Proposition 5.2, p.22

import Mathlib
import Definitions.Def_RandOrderCSP_compPartition
import Definitions.Def_RandOrderCSP_blockVol
import Definitions.Def_RandOrderCSP_fourierCoeff

namespace RandOrderCSP

/-- **Proposition 5.2 (boundary support on a forest).** Singer, Tulsiani, Velusamy, *A dichotomy theorem
for approximating CSPs in random-order streams*, STOC 2027 submission (manuscript sha256 3aca9d2f…),
Proposition 5.2, p.22.

**Formalization Note.** `Ω` is singleton-free when every row has support size different from `1`;
`∂_H Ω` is component-singleton-free when its support is in `SF_{𝒫_H}` (p.22). -/
theorem proposition_5_2 {k q : ℕ} [NeZero q] (hq : 2 ≤ q) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (H : Hypergraph k V E) (hH : H.Acy) (Ω : E × Fin k → ZMod q)
    (hΩ : ∀ j, (Finset.univ.filter fun ℓ => Ω (j, ℓ) ≠ 0).card ≠ 1) :
    IsSF H.compPartition (vsupp (H.boundary Ω)) ∧ (Ω ≠ 0 → H.boundary Ω ≠ 0) := by sorry

end RandOrderCSP
