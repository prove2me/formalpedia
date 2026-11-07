-- Prove2me | Theorems.Thm_StableCount_proposition_2_5
-- name    : StableCount.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:03.95577+00:00
-- url     : https://prove2.me/theorems/af55b301-6944-49d0-86b3-4147a68eb93c
-- title:
--   Proposition 2.5 — normalization preserves stable matchings, stable partners and maximal chains
-- statement:
--   Let $I$ be an instance and $\hat I$ its normalization. Every stable matching of $I$ is stable in $\hat I$. The two instances have the same stable partners for every person, and every maximal chain of $I$ remains a maximal chain of $\hat I$ with the same rotations. In particular, $\hat I$ is normalized and
--   $$
--   s(I)\le s(\hat I).
--   $$
--   This is what reduces the counting problem to normalized instances, without changing any person's number of stable partners.
--
--   Differences from the source:
--   - encoding: n men and n women, each with a strict ranking of the other set → the published StableMatching.Instance n: rank bijections on Fin n, with men and women both indexed by Fin n; reason: same instances
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: "with the same rotations" → for a maximal chain μ of I, each exposed ρ of a step is exposed at the same matching in normalize I; reason: elimination does not depend on the instance, so the same ρ gives the same step
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Proposition 2.5, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_StableCount_Rotation

namespace StableCount

open StableMatching

/-- Proposition 2.5 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Proposition 2.5, p.9). Every stable matching of `I` is stable in `Î`. The
two instances have the same stable partners for every person, and every maximal chain of `I` remains a
maximal chain of `Î` with the same rotations. In particular, `Î` is normalized and `s(I) ≤ s(Î)`. -/
theorem proposition_2_5 {n : ℕ} (I : Instance n) :
    (∀ μ, I.IsStable μ → (normalize I).IsStable μ) ∧
    (∀ v, manPartners (normalize I) v = manPartners I v) ∧
    (∀ w, womanPartners (normalize I) w = womanPartners I w) ∧
    (∀ {R : ℕ} (μ : Fin (R + 1) → Matching n), IsMaximalChain I μ →
      IsMaximalChain (normalize I) μ ∧
        ∀ (i : Fin R) (ρ : Rot n), IsExposed I (μ i.castSucc) ρ →
          IsElim (μ i.castSucc) ρ (μ i.succ) → IsExposed (normalize I) (μ i.castSucc) ρ) ∧
    IsNormalized (normalize I) ∧ numStable I ≤ numStable (normalize I) := by sorry

end StableCount
