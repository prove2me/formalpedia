-- Prove2me | Theorems.Thm_StableCount_lemma_2_4
-- name    : StableCount.lemma_2_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:48:53.184873+00:00
-- url     : https://prove2.me/theorems/1b39ac47-1371-4113-ae06-f8d5dba354ad
-- title:
--   Lemma 2.4 — a partner-exchange history with no returns is a maximal chain of a normalized instance
-- statement:
--   Fix $n$ men and $n$ women, and let $\mu_0,\dots,\mu_R$ be perfect matchings between them. Suppose each matching is obtained from the preceding one by cyclically exchanging the partners of at least two men, and no man or woman returns to a partner after leaving them. Then there is a normalized instance $I$ in which $\mu_0,\dots,\mu_R$ is a maximal chain of stable matchings, with each prescribed exchange eliminating an exposed rotation, and the stable pairs of $I$ are exactly the pairs appearing in these matchings.
--
--   This is the construction that keeps the induction of the paper inside normalized instances: any retained part of a chain is again the chain of a normalized instance.
--
--   Differences from the source:
--   - encoding: n men and n women, each with a strict ranking of the other set → the published StableMatching.Instance n: rank bijections on Fin n, with men and women both indexed by Fin n; reason: same instances
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: "cyclically exchanging the partners of at least two men" → ∃ c : Perm (Fin n), c.IsCycle ∧ ∀ v, μ (i+1) v = μ i (c v); reason: IsCycle is a single nontrivial cycle, so at least two men move
--   - encoding: "no man or woman returns to a partner after leaving them" → for i ≤ j ≤ k: μ i v = μ k v → μ j v = μ i v, and the same for μ.symm; reason: the two statements say the same
--   - encoding: "the stable pairs of I are exactly the pairs appearing in these matchings" → ∀ m w, w ∈ manPartners I m ↔ ∃ i, μ i m = w; reason: a pair is one man and one woman, so the statement on men covers women
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 2.4, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_StableCount_Rotation

namespace StableCount

open StableMatching

/-- Lemma 2.4 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 2.4, p.9). Let `µ₀,…,µ_R` be perfect matchings, each obtained from the
preceding one by cyclically exchanging the partners of at least two men, with no man or woman
returning to a partner after leaving them. Then there is a normalized instance in which `µ₀,…,µ_R` is a
maximal chain of stable matchings, with each prescribed exchange eliminating an exposed rotation, and
whose stable pairs are exactly the pairs appearing in these matchings.

**Formalization Note** "Cyclically exchanging the partners of at least two men" is `Equiv.Perm.IsCycle`,
a single nontrivial cycle `c` of the men with `µ_{i+1}(v) = µ_i(c v)`. -/
theorem lemma_2_4 {n R : ℕ} (μ : Fin (R + 1) → Matching n)
    (hcycle : ∀ i : Fin R, ∃ c : Equiv.Perm (Fin n), c.IsCycle ∧
      ∀ v, μ i.succ v = μ i.castSucc (c v))
    (hman : ∀ (v : Fin n) (i j k : Fin (R + 1)), i ≤ j → j ≤ k → μ i v = μ k v → μ j v = μ i v)
    (hwoman : ∀ (w : Fin n) (i j k : Fin (R + 1)), i ≤ j → j ≤ k →
      (μ i).symm w = (μ k).symm w → (μ j).symm w = (μ i).symm w) :
    ∃ I : Instance n, IsNormalized I ∧ IsMaximalChain I μ ∧
      (∀ i : Fin R, ∃ ρ, IsExposed I (μ i.castSucc) ρ ∧ IsElim (μ i.castSucc) ρ (μ i.succ)) ∧
      ∀ m w, w ∈ manPartners I m ↔ ∃ i, μ i m = w := by sorry

end StableCount
