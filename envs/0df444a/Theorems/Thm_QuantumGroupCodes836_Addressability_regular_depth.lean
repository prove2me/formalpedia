-- Prove2me | Theorems.Thm_QuantumGroupCodes836_Addressability_regular_depth
-- name    : QuantumGroupCodes836.Addressability.regular_depth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T17:13:42.660197+00:00
-- url     : https://prove2.me/theorems/249b13bc-0db2-4e44-9209-fe819b545dae
-- title:
--   Corollary 3.5 — regular addressability (corrected: m blocks; dual-distance hypothesis)
-- statement:
--   Take one deleted orbit in the corrected Theorem 3.4. The actual constructed code is regular, has full addressability for weighted interblock $C^{m-1}Z$ gates, and every finite such logical circuit on the fixed $m$ code blocks has an equivalent physical implementation satisfying
--
--   $$\operatorname{depth}_{\mathrm{phys}}\le k_Q^{m-1}.$$
--
--   This is the exact bound, with no extra factor or guessed constant. The printed $n$-block statement is repaired to the $m$-block statement proved on p.14.
--
--   Differences from the source:
--   - encoding: CSS codes and module-linear sections → actual normalized coset subspaces and equivariant linear sections of actual quotients; reason: these are equivalent finite-coordinate models, with computed logical dimension and quotient-weight distance
--   - correction: d(C^perp)>|G| → d(C^perp)>r|G|; reason: C2: three independent length-four repetition blocks with trivial G and two selected singleton orbits satisfy the printed assumptions but give logical dimension 1 instead of 2
--   - correction: an arbitrary interblock circuit on n code blocks has depth at most k^(m-1) → an arbitrary interblock circuit on m code blocks has depth at most k^(m-1); reason: C4: the length-eight binary repetition-pair example has k=1 but a seven-neighbor CZ star needs more than one matching layer
--   - generalization: Q as in Theorem 3.4 with its encoding → the encoding of Q is the canonical one, E(c_L) = π(c_{L̄}) for c ∈ C; reason: this is the E of Lemma 3.8; the Lean conclusion implies the source one
-- source:
--   Virgile Guemard, Jean Gasnier, STOC 2027 submission #836 (October 2026), Corollary 3.5, p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/836.pdf

import Definitions.Def_QuantumGroupCodes836_Addressability_Construction

set_option autoImplicit false
open scoped Classical

namespace QuantumGroupCodes836.Addressability

theorem regular_depth {F G : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    [Group G] [Fintype G] {n m : ℕ} (C : Code F (Fin n)) (A : CodeAction F (Fin n) G C)
    (p : Fin 1 → Fin n) (u : Fin n → F) (h : ConstructionAssumptions C A p m u) :
    ∃ Q : GroupCode F, ConstructionOutput C A p Q ∧ FreeQuantum Q.physical 1 ∧
      FullyAddressable Q.code m ∧ ∀ circuit : List (InterblockGate F m Q.code.toCSS.logicalDimension m),
        DepthAtMost Q.code circuit (Q.code.toCSS.logicalDimension ^ (m - 1)) := by sorry

end QuantumGroupCodes836.Addressability
