-- Prove2me | Theorems.Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
-- name    : ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/10a9d7d7-29fc-5859-a148-c8ae34ef1de7
-- title:
--   p-adic decomposition subgroup lies in closure of local image
-- statement:
--   Let $p$ be a prime. Write $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let [`padicEmbedding p`](def/GaloisRep_CompletionBridge.html#L17) $\colon \overline{\mathbb{Q}} \to$ `PadicAlgCl p` be the $\mathbb{Q}$-algebra map obtained by lifting $\overline{\mathbb{Q}}$ into the algebraically closed field `PadicAlgCl p` over $\mathbb{Q}$, and let [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) be the valuation subring of $\overline{\mathbb{Q}}$ obtained by pulling back, along this embedding, the valuation subring of `PadicAlgCl p` attached to its $\mathbb{R}_{\ge 0}$-valued valuation `Valued.v`. Let [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) be the group homomorphism from $\mathrm{Gal}(\mathrm{PadicAlgCl}\,p/\mathbb{Q}_p)$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ that first restricts scalars from $\mathbb{Q}_p$ to $\mathbb{Q}$ and then restricts a $\mathbb{Q}$-automorphism to the normal subextension $\overline{\mathbb{Q}}$. The assertion is an inclusion of subgroups of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$: the decomposition subgroup of [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) over $\mathbb{Q}$, that is the subgroup of automorphisms carrying this valuation subring to itself, is contained in the topological closure (for the Krull topology on the absolute Galois group) of the image of [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41). Only the inclusion into the closure is claimed, not equality with the image.
--
--   This is the density half of the comparison between the decomposition group at the chosen $p$-adic place of $\overline{\mathbb{Q}}$ and the image of the local Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$, the reverse inclusion (image inside the decomposition group) being part of the completion bridge itself; classically the two groups coincide. It feeds the extraction of a local automorphism realising a given global element on any prescribed algebraic number, and through that the local-at-$p$ splitting steps used in the level arithmetic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal.lean

import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
    (p : ℕ) [Fact p.Prime] :
    ((padicPlace p).decompositionSubgroup ℚ
        : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      ≤ (MonoidHom.range (localGaloisToGlobal p)).topologicalClosure := by sorry
