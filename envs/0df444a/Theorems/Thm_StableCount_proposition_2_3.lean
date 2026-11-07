-- Prove2me | Theorems.Thm_StableCount_proposition_2_3
-- name    : StableCount.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:06.578129+00:00
-- url     : https://prove2.me/theorems/9f015ad8-b85d-48d1-bdad-a2b61f4011f4
-- title:
--   Proposition 2.3 — maximal chains eliminate every rotation exactly once; partners change to the next stable partner
-- statement:
--   Let $I$ be an instance, and $\Pi$ its set of rotations.
--
--   1. Every maximal chain from $\mu_M$ to $\mu_W$ eliminates every rotation in $\Pi$ exactly once. Consequently, every such chain has $|\Pi|$ steps.
--   2. When a man participates in a rotation, his partner changes to the next woman in his list of stable partners, ordered from most to least preferred. When a woman participates, her partner changes to the next man in her list of stable partners, ordered from least to most preferred.
--
--   This is the structure of chains used throughout: along a maximal chain each person receives every stable partner without skipping any. The paper cites it from Gusfield (1987) and Cai, Thomas (2019).
--
--   **Formalization Note** The rotation of each chain step is named, as an exposed rotation whose elimination gives the next matching. "Next" means that the new partner is itself a stable partner, is worse (for a man) or better (for a woman), and that no stable partner lies strictly between.
--
--   Differences from the source:
--   - encoding: n men and n women, each with a strict ranking of the other set → the published StableMatching.Instance n: rank bijections on Fin n, with men and women both indexed by Fin n; reason: same instances
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: "eliminates every rotation in Π exactly once" with |Π| steps → ∃ rot : Fin R → Rot n naming the step rotations, injective, with range Π, R = (Π).ncard, and a clause that Π is finite; reason: the same statement; the step rotations come from Lemma 2.2, and finiteness makes ncard meaningful
--   - encoding: "participates in a rotation … the next" partner → for every exposed ρ in a stable μ, with ν = μ/ρ: the new partner is a stable partner, on the correct side, and no stable partner lies strictly between; reason: this is the reading of "next"; chain steps are such ρ by clause (i)
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Proposition 2.3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_StableCount_Rotation

namespace StableCount

open StableMatching

/-- Proposition 2.3 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Proposition 2.3, p.8; cited there from Gusfield 1987).
(i) Every maximal chain from `µ_M` to `µ_W` eliminates every rotation in `Π` exactly once, so it has
`|Π|` steps. (ii) When a man participates in a rotation, his partner changes to the next woman in his
list of stable partners, from most to least preferred; when a woman participates, her partner changes
to the next man in her list, from least to most preferred.

**Formalization Note** Clause (i) names the rotation of each step, as an exposed rotation whose
elimination gives the next matching. `Π` is finite, which makes `Set.ncard` meaningful. Clause (ii) is
stated for every exposed rotation of every stable matching, which covers every chain step by (i). The new
partner is itself a stable partner ("changes to the next woman in his list of stable partners"), and no
stable partner lies strictly between the old and the new one. -/
theorem proposition_2_3 {n : ℕ} (I : Instance n) :
    (Pi I).Finite ∧
    (∀ {R : ℕ} (μ : Fin (R + 1) → Matching n), IsMaximalChain I μ →
      ∃ rot : Fin R → Rot n,
        (∀ i, IsExposed I (μ i.castSucc) (rot i) ∧ IsElim (μ i.castSucc) (rot i) (μ i.succ)) ∧
        Function.Injective rot ∧ Set.range rot = Pi I ∧ R = (Pi I).ncard) ∧
    (∀ (μ ν : Matching n) (ρ : Rot n), IsExposed I μ ρ → IsElim μ ρ ν →
      (∀ v, μ v ≠ ν v →
        ν v ∈ manPartners I v ∧ I.manPrefers v (μ v) (ν v) ∧
          ∀ w ∈ manPartners I v, ¬ (I.manPrefers v (μ v) w ∧ I.manPrefers v w (ν v))) ∧
      (∀ w, μ.symm w ≠ ν.symm w →
        ν.symm w ∈ womanPartners I w ∧ I.womanPrefers w (ν.symm w) (μ.symm w) ∧
          ∀ v ∈ womanPartners I w,
            ¬ (I.womanPrefers w (ν.symm w) v ∧ I.womanPrefers w v (μ.symm w)))) := by sorry

end StableCount
