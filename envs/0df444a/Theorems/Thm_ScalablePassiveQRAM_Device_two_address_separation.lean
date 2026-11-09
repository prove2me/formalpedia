-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_two_address_separation
-- name    : ScalablePassiveQRAM.Device.two_address_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:36.65771+00:00
-- url     : https://prove2.me/theorems/bca3c730-bbb7-42cf-b622-783a214da53a
-- title:
--   Lemma 7 — Two-address separation
-- statement:
--   Fix $n\ge1$, $\Omega>0$, a pinning coefficient $\Delta$, database $D$, and two addresses $x,y$, which may coincide. For either $z=x$ or $z=y$, the constructed tensor embedding $B_z$ includes both initial bus values, vacuum on $F_{xy}\setminus F_z$, and the entire outside Hilbert space. Every footprint has $F_n=10n^2+14n+12$ rails.
--
--   $$H_DB_z=B_z(H_{{\rm br},z}\otimes I+I\otimes H_{{\rm out},D}^{xy}),$$
--   $$K_DB_z=B_z((H_{{\rm br},z}+(n+2)\Delta I)\otimes I+I\otimes K_{{\rm out},D}^{xy}).$$
--
--   The embeddings are isometries, and the adjoint intertwinings also hold, giving reduction. The same outside compression is used for both addresses; $K_{\rm out}=H_{\rm out}+P_{\rm out}$ with the explicit outside on-site sum. Any retained root record is untouched by these sector operators. This is separation with arbitrary excited outside states.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - generalization: positive on-site energy splitting Δ → any real Δ in the exact algebraic pinning and separation identities; reason: commutation, the common eigenvalue, and unitary phase identities are algebraic in Δ and specialize to every physical positive splitting
--   - encoding: the final sentence "any retained root address record R is an additional untouched tensor factor" → not a clause of this statement; the sector operators act on ports and auxiliaries only, and the recorded-interface Hamiltonian recordedHamiltonian is by definition the identity on R; reason: the record is untouched by construction, so the clause holds definitionally on every instance
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Lemma 7, p. 27. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance two_address_separationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance two_address_separationDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem two_address_separation (n : ℕ) (hn : 1 ≤ n) (Ω Δ : ℝ) (hΩ : 0 < Ω)
    (D : Database n) (x y : Address n) :
    (∀ z : Address n, (footprint n z).card = footprintSize n) ∧
    (∀ z ∈ ({x,y} : Finset (Address n)),
      (pairEmbedding n D x y z).conjTranspose * pairEmbedding n D x y z = 1 ∧
      sectorMatrix n D (hamiltonian n Ω) * pairEmbedding n D x y z =
        pairEmbedding n D x y z * pairGenerator n Ω D x y ∧
      sectorHamiltonian n Ω Δ D * pairEmbedding n D x y z =
        pairEmbedding n D x y z * (pairGenerator n Ω D x y + pairPinning n Δ x y)) ∧
    (∀ z ∈ ({x,y} : Finset (Address n)),
      (pairEmbedding n D x y z).conjTranspose * sectorMatrix n D (hamiltonian n Ω) =
        pairGenerator n Ω D x y * (pairEmbedding n D x y z).conjTranspose ∧
      (pairEmbedding n D x y z).conjTranspose * sectorHamiltonian n Ω Δ D =
        (pairGenerator n Ω D x y + pairPinning n Δ x y) * (pairEmbedding n D x y z).conjTranspose) := by sorry

end ScalablePassiveQRAM.Device
