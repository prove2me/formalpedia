-- Prove2me | Theorems.Thm_SunGroupIso_Class2_corollary_4_6
-- name    : SunGroupIso.Class2.corollary_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:05.448411+00:00
-- url     : https://prove2.me/theorems/db45784a-8d4e-482a-b511-0e271945f4e5
-- title:
--   Corollary 4.6 — at most |G|^{2k} split-off tuples, all computable in time |G|^{O(k)}
-- statement:
--   Let $G$ be a finite abelian $p$-group. (Count) The tuples $(g_1,\dots,g_k,U)$ with $G=\langle g_1\rangle\oplus\cdots\oplus\langle g_k\rangle\oplus U$ and $\mathrm{rank}(U)=\mathrm{rank}(G)-k$ number at most $|G|^{2k}$. (Algorithm) One Turing machine and one constant $C$ serve every prime $p$, every labelled finite abelian $p$-group of order $N$ and every $k$: on the Cayley table and $k$ the machine outputs, within $N^{Ck}$ steps, a duplicate-free list of exactly these tuples.
--
--   Differences from the source:
--   - encoding: an algorithm, no machine model fixed; inputs are groups, restrictions, tensors or matrix tuples → one Mathlib multi-stack Turing machine run through the published HMBinPacking.OutputsWithin, on binary codes built from the published encodeNat (groups by labelled Cayley tables, every labelling quantified); reason: Turing machines and RAMs simulate each other with polynomial overhead; any standard code differs polynomially
--   - reading: 'there is an algorithm … in time p^{O(·)}' (the O-constant and the algorithm unspecified in their dependence on p) → one machine and one constant C chosen before the prime p and every other input; reason: the paper presents 'a general algorithm that works for all the possible p-groups of class 2' (p. 8, PDF p. 10); the uniform reading is the stronger one
--   - encoding: rank(U) = rank(G) − k → abRank U + k = abRank G; reason: avoids natural-number subtraction; the same tuples, since the source's equation already forces k ≤ rank(G)
--   - encoding: time |G|^{O(k)} → N^(C*k), including k = 0; reason: the literal bound is retained; the boundary input-size issue is recorded in INSIGHTS.yaml I4, not repaired in the item
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Corollary 4.6, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Corollary 4.6** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Corollary 4.6, p. 16, PDF p. 18). Let `G` be a finite abelian `p`-group.
There are at most `|G|^{2k}` tuples `(g_1, …, g_k, U)` with `G = ⟨g_1⟩ ⊕ ⋯ ⊕ ⟨g_k⟩ ⊕ U` and
`rank(U) = rank(G) − k`. Furthermore, one algorithm computes all these tuples in time `|G|^{O(k)}`. -/
theorem corollary_4_6 :
    (∀ {p : ℕ}, p.Prime → ∀ {G : Type*} [CommGroup G] [Finite G], IsPGroup p G → ∀ k : ℕ,
      {x : (Fin k → G) × Subgroup G |
          DecompWith ⊤ x.1 x.2 ∧ abRank x.2 + k = abRank (⊤ : Subgroup G)}.ncard ≤
        Nat.card G ^ (2 * k)) ∧
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (p N : ℕ) (G : Type) [CommGroup G] (e : G ≃ Fin N), p.Prime → IsPGroup p G → ∀ k : ℕ,
        ∃ L : List ((Fin k → G) × Subgroup G), L.Nodup ∧
          (∀ x, x ∈ L ↔ DecompWith ⊤ x.1 x.2 ∧ abRank x.2 + k = abRank (⊤ : Subgroup G)) ∧
          HMBinPacking.OutputsWithin M (encGroup e ++ encodeNat k)
            (encList (fun x => encVec (encElem e) x.1 ++ encSet e x.2) L)
            (N ^ (C * k)) := by sorry

end SunGroupIso.Class2
