-- Prove2me | Theorems.Thm_StableCount_lemma_3_1
-- name    : StableCount.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:57.916225+00:00
-- url     : https://prove2.me/theorems/966561d3-70a6-43e8-bbe8-4f401ccc7273
-- title:
--   Lemma 3.1 (Irving–Leather) — downsets of the full rotation poset biject with stable matchings
-- statement:
--   Let $I$ be an instance and $Q_f=(\Pi,\prec_f)$ its full rotation poset. For every downset $D$ of $Q_f$, eliminating the rotations in $D$ from $\mu_M$, in any order consistent with $Q_f$, gives a stable matching $\mu_D$. The map $D\mapsto\mu_D$ is a bijection between the downsets of $Q_f$ and the stable matchings of $I$. In particular,
--   $$
--   s(I)=J(Q_f).
--   $$
--   This is the classical representation of stable matchings by rotations, which the paper cites from Irving and Leather (1986). It turns counting stable matchings into counting downsets.
--
--   **Formalization Note** The instance is arbitrary. A consistent order is a list of $D$ in which $\rho$ precedes $\sigma$ whenever $\rho\prec_f\sigma$.
--
--   Differences from the source:
--   - encoding: n men and n women, each with a strict ranking of the other set → the published StableMatching.Instance n: rank bijections on Fin n, with men and women both indexed by Fin n; reason: same instances
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: "in any order consistent with Q_f" and J(Q_f) → the existence of a consistent order is stated with the clause on all of them, and the family of downsets is stated finite, with J(Q_f) its ncard; reason: ≺f is a strict partial order on a finite set, so an order exists; the clauses keep "any order" and ncard from being empty readings
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 3.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_StableCount_Rotation

namespace StableCount

open StableMatching

/-- Lemma 3.1 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 3.1, p.10; cited there from Irving, Leather 1986). For every downset `D` of
the full rotation poset `Q_f`, eliminating the rotations of `D` from `µ_M`, in any order consistent with
`Q_f`, gives a stable matching `µ_D`. The map `D ↦ µ_D` is a bijection between the downsets of `Q_f` and the
stable matchings of `I`. In particular, `s(I) = J(Q_f)`.

**Formalization Note** The instance is arbitrary. A consistent order exists for each downset, which is
stated so that the clause on "any order" is not vacuous. The family of downsets is finite, which makes
`Set.ncard` meaningful. -/
theorem lemma_3_1 {n : ℕ} (I : Instance n) :
    ∃ μM, IsManOptimal I μM ∧
      ∃ f : {D : Set (Rot n) // IsFullDownset I D} ≃ {μ : Matching n // I.IsStable μ},
        (∀ D, (∃ l, IsConsistentOrder I D.1 l) ∧
          ∀ l, IsConsistentOrder I D.1 l → IsElimSeq I μM l (f D).1) ∧
        {D : Set (Rot n) | IsFullDownset I D}.Finite ∧
        numStable I = {D : Set (Rot n) | IsFullDownset I D}.ncard := by sorry

end StableCount
