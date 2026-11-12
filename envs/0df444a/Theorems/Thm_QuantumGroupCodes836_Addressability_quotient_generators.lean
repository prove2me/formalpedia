-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_quotient_generators
-- name    : QuantumGroupCodes836.Addressability.quotient_generators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:13:48.099411+00:00
-- url     : https://prove2.me/theorems/53d26d3d-299c-491c-bea5-4f790e6264bb
-- title:
--   Lemma 3.7 — quotient, generators and section (corrected: dual-distance hypothesis)
-- statement:
--   Use the characteristic-two construction of Theorem 3.4, with $L$ a union of $r$ distinct free orbits of size $\ell$ and the corrected condition $d(C^\perp)>r\ell$. Restriction to $L$ is surjective; restriction to the remaining punctured coordinates is bijective. The shortened image lies inside the punctured image, and
--
--   $$C_1/C_0^\perp\cong F[G]^r.$$
--
--   There are $r$ codeword generators whose full $L$-restrictions are the orbit-coordinate unit vectors. Their group translates give the stated direct-sum basis of the quotient. An equivariant linear section sends each basis class to the corresponding punctured codeword, exactly as Equation (7).
--
--   Differences from the source:
--   - encoding: CSS codes and module-linear sections → actual normalized coset subspaces and equivariant linear sections of actual quotients; reason: these are equivalent finite-coordinate models, with computed logical dimension and quotient-weight distance
--   - correction: d(C^perp)>|G| → d(C^perp)>r|G|; reason: C2: three independent length-four repetition blocks with trivial G and two selected singleton orbits satisfy the printed assumptions but give logical dimension 1 instead of 2
--   - encoding: the module direct sum and isomorphism → an explicit group-translate basis and bijective restriction map; reason: the restriction maps are already linear and equivariant; the basis specifies the direct sum without extra hypotheses
--   - reading: π_{L_i}(g_i) = (1,0,…,0) → π_L(g_i) is the indicator of the representative p_i (zero on the other orbits); reason: the proof uses that the G-translates of g_1,…,g_r form the canonical basis of F_q^L, which requires vanishing on the other orbits
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Lemma 3.7, p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Construction

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem quotient_generators {F G : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] [Group G] [Fintype G]
    {n r m : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (u : Fin n → F) (h : ConstructionAssumptions C A p m u) :
    let L := chosenOrbits A p
    Function.Surjective (fun c : C => restrictLinear (F := F) L (c : Fin n → F)) ∧
    Function.Bijective (punctureWord C L) ∧ QuotientGenerators C A p := by sorry

end QuantumGroupCodes836.Addressability
