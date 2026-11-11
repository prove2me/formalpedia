-- Prove2me | Theorems.Thm_PermDiameter_Binary_lemma_2_3
-- name    : PermDiameter.Binary.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:12.187203+00:00
-- url     : https://prove2.me/theorems/bbc0b646-1713-4f77-8525-d944b779a13a
-- title:
--   Lemma 2.3 — Schreier–Sims in polynomial time: membership, a generating set of diameter $\le|\Omega|$, stabilizer generators of diameter $\le|\Omega|$ with left and right transversals
-- statement:
--   Let a permutation group $G\le\mathrm{Sym}(\Omega)$, $|\Omega|=d$, be given by a generating set $\Sigma$ (permutations as image lists). The following tasks can be performed in polynomial time.
--
--   1. Test membership in $G$ of any given permutation $g\in\mathrm{Sym}(\Omega)$.
--   2. Compute a generating set $\bar\Sigma$ of $G$ with $\operatorname{diam}(G,\bar\Sigma)\le|\Omega|$.
--   3. Compute, for each point $\omega\in\Omega$, a generating set $\Sigma_\omega$ of $\mathrm{Stab}_G(\omega)$ with $\operatorname{diam}(\mathrm{Stab}_G(\omega),\Sigma_\omega)\le|\Omega|$, as well as a left and a right transversal of $\mathrm{Stab}_G(\omega)$ in $G$.
--
--   $$\exists\ \text{poly-time } \mathsf{mem},\ \bar\Sigma(\cdot),\ (\Sigma_\omega,LT_\omega,RT_\omega)(\cdot):\quad \mathsf{mem}(\Sigma,g)\iff g\in\langle\Sigma\rangle,\ \ \langle\bar\Sigma\rangle=G,\ \operatorname{diam}(G,\bar\Sigma)\le d,\ \dots$$
--
--   These are the standard consequences of a base and strong generating set; the reduction uses them to compute the local generators and transversals of Step 2 and to single out the entries.
--
--   **Formalization Note.** "Polynomial time" is `Turing.TM2ComputableInPolyTime` on the encodings of `PermDiameter.Binary.Problems`; the membership test is a `Bool`-valued map with output `[b]`. Generating sets and transversals are output as lists (the set of their entries); the third task outputs the table of all $d$ triples at once.
--
--   Differences from the source:
--   - encoding: Ω = [1, d], permutations as image lists, "polynomial time" → Ω = Fin d, encodings encGenSet/encMemQuery/encStabTable, Turing.TM2ComputableInPolyTime; reason: the paper's input format (p. 10) with an explicit machine model
--   - encoding: "compute, for each point ω" → one map returning the triples of all d points; reason: d per-point computations are polynomial iff all of them together are
--   - encoding: permutations compose left to right (paper) → Mathlib's Equiv.Perm composes right to left; reason: generated subgroups, stabilizers and diameters are unchanged, and the statement asks for both a left and a right transversal, which the change of convention swaps
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), pp. 10–11, Lemma 2.3

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Problems

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Lemma 2.3** (Schreier–Sims consequences). On input of a generating set of a permutation
group `G ≤ Sym(d)`, in polynomial time one can (1) test membership in `G` of any permutation;
(2) compute a generating set `Σ̄` of `G` with `diam(G, Σ̄) ≤ d`; (3) compute, for every point `ω`,
a generating set `Σ_ω` of `Stab_G(ω)` with `diam(Stab_G(ω), Σ_ω) ≤ d`, and a left and a right
transversal of `Stab_G(ω)` in `G`. -/
theorem lemma_2_3 :
    (∃ mem : MemQuery → Bool,
        Nonempty (Turing.TM2ComputableInPolyTime encMemQuery (fun b : Bool => [b]) mem) ∧
        ∀ x : MemQuery, mem x = true ↔ x.2.2 ∈ Subgroup.closure {a | a ∈ x.2.1}) ∧
    (∃ F : (d : ℕ) → List (Perm (Fin d)) → List (Perm (Fin d)),
        Nonempty (Turing.TM2ComputableInPolyTime encGenSet encGenSet
          (fun x : GenSet => (⟨x.1, F x.1 x.2⟩ : GenSet))) ∧
        ∀ (d : ℕ) (L : List (Perm (Fin d))),
          Subgroup.closure {a | a ∈ F d L} = Subgroup.closure {a | a ∈ L} ∧
          diamOn (Subgroup.closure {a | a ∈ L} : Set (Perm (Fin d))) {a | a ∈ F d L} ≤ (d : ℕ∞)) ∧
    (∃ F : (d : ℕ) → List (Perm (Fin d)) → Fin d →
          List (Perm (Fin d)) × List (Perm (Fin d)) × List (Perm (Fin d)),
        Nonempty (Turing.TM2ComputableInPolyTime encGenSet encStabTable
          (fun x : GenSet => (⟨x.1, F x.1 x.2⟩ : StabTable))) ∧
        ∀ (d : ℕ) (L : List (Perm (Fin d))) (ω : Fin d),
          Subgroup.closure {a | a ∈ (F d L ω).1} =
              Subgroup.closure {a | a ∈ L} ⊓ MulAction.stabilizer (Perm (Fin d)) ω ∧
          diamOn ((Subgroup.closure {a | a ∈ L} ⊓ MulAction.stabilizer (Perm (Fin d)) ω :
              Subgroup (Perm (Fin d))) : Set (Perm (Fin d))) {a | a ∈ (F d L ω).1} ≤ (d : ℕ∞) ∧
          IsLeftTransversal {a | a ∈ (F d L ω).2.1}
            (Subgroup.closure {a | a ∈ L} ⊓ MulAction.stabilizer (Perm (Fin d)) ω)
            (Subgroup.closure {a | a ∈ L}) ∧
          IsRightTransversal {a | a ∈ (F d L ω).2.2}
            (Subgroup.closure {a | a ∈ L} ⊓ MulAction.stabilizer (Perm (Fin d)) ω)
            (Subgroup.closure {a | a ∈ L})) := by sorry

end PermDiameter.Binary
