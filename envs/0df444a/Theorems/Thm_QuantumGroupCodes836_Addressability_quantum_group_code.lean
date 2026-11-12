-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_quantum_group_code
-- name    : QuantumGroupCodes836.Addressability.quantum_group_code
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:13:27.190341+00:00
-- url     : https://prove2.me/theorems/d0ed8fb1-f0bc-45b8-84ee-772052f12fbf
-- title:
--   Theorem 3.4 — quantum group code and gates (corrected: dual-distance hypothesis)
-- statement:
--   Let $C\subseteq F^n$ satisfy the source construction hypotheses: a specified free quasi-$G$ action, $m\ge2$, actual dimension $k>r\ell$, common nonzero weights for the $m$- and $2$-multiplication properties, and the corrected $d(C^\perp)>r\ell$. Delete $r$ distinct full orbits $L$ and construct $C_0=(C_{L=0})^\perp$, $C_1=C_J$. Then the actual CSS code is free of module rank $r$ and has
--
--   $$n_Q=n-r\ell,\quad k_Q=r\ell,\quad d_Q\ge\min\{d(C),d(C^\perp)\}-r\ell.$$
--
--   An encoding tied to the input action implements in depth one every shared-shift product across arbitrary logical subsets and every within-orbit weighted tuple. Physical layers must have disjoint supports. All four source conclusions are retained.
--
--   Differences from the source:
--   - encoding: CSS codes and module-linear sections → actual normalized coset subspaces and equivariant linear sections of actual quotients; reason: these are equivalent finite-coordinate models, with computed logical dimension and quotient-weight distance
--   - correction: d(C^perp)>|G| → d(C^perp)>r|G|; reason: C2: three independent length-four repetition blocks with trivial G and two selected singleton orbits satisfy the printed assumptions but give logical dimension 1 instead of 2
--   - generalization: the displayed gate clauses use unit coefficients → arbitrary field coefficients are allowed; reason: Lemma 3.10 supplies arbitrary modulation weights; unit coefficients recover every displayed source gate
--   - generalization: there exists an encoding map E → the encoding of Q is the canonical one, E(c_L) = π(c_{L̄}) for c ∈ C; reason: this is the E of Lemma 3.8; the Lean conclusion implies the source one
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Theorem 3.4, p.10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Construction

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem quantum_group_code {F G : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] [Group G] [Fintype G]
    {n r m : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin r → Fin n) (u : Fin n → F) (h : ConstructionAssumptions C A p m u) :
    ∃ Q : GroupCode F, ConstructionOutput C A p Q ∧ FreeQuantum Q.physical r ∧
      Q.code.n = n - r * Fintype.card G ∧
      Q.code.toCSS.logicalDimension = r * Fintype.card G ∧
      min (distance C) (distance (dual C)) - (r * Fintype.card G : ℕ∞) ≤ Q.code.toCSS.quantumDistance ∧
      OrbitAddressable Q m := by sorry

end QuantumGroupCodes836.Addressability
