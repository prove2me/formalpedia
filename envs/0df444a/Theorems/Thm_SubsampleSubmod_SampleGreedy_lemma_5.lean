-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_5
-- name    : SubsampleSubmod.SampleGreedy.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:03.570166+00:00
-- url     : https://prove2.me/theorems/89a2b64e-faa5-4efc-81b7-2ef0e1437b9c
-- title:
--   Lemma 5, p. 11 — throughout Algorithm 2, O is independent, S ⊆ O, and O ∖ S consists of unconsidered elements
-- statement:
--   Let $(\mathcal N, \mathcal I)$ be an independence system, $T \in \mathcal I$, $f$ any set function and $B$ any outcome of the coins. Run Algorithm 2 from $O = T$. After every number $j \ge 0$ of iterations the following hold:
--
--   1. (P1) $O \in \mathcal I$;
--   2. (P2) $S \subseteq O$;
--   3. (P3) every element of $O \setminus S$ has not yet been considered by Algorithm 2.
--
--   These invariants are what make the removal step of line 6 well defined and drive the deterministic bound of Lemma 6.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 11, Lemma 5 (properties P1–P3)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 5 (p. 11). Throughout Algorithm 2 (after every number `j` of iterations), started from an
independent `T`: (P1) `O` is independent; (P2) `S ⊆ O`; (P3) every element of `O \ S` has not yet
been considered. -/
theorem lemma_5 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hI : IsIndepSystem I) (T : Finset α) (hT : I T) (B : Finset α)
    (j : ℕ) :
    I ((alg2Step f I B)^[j] (alg2Init T)).O ∧
    ((alg2Step f I B)^[j] (alg2Init T)).S ⊆ ((alg2Step f I B)^[j] (alg2Init T)).O ∧
    ∀ v ∈ ((alg2Step f I B)^[j] (alg2Init T)).O \ ((alg2Step f I B)^[j] (alg2Init T)).S,
      v ∉ ((alg2Step f I B)^[j] (alg2Init T)).considered := by sorry

end SubsampleSubmod.SampleGreedy
