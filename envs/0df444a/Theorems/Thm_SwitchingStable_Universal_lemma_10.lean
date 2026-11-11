-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_10
-- name    : SwitchingStable.Universal.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:16.614196+00:00
-- url     : https://prove2.me/theorems/56253a3b-b26a-4243-b1a4-b32c3c55e034
-- title:
--   Lemma 10 — Third-boundary failure injection
-- statement:
--   Fix either direction in the promoted market. A tail is a third-boundary failure precisely when its third boundary exists and no man outside the coordinate and its first three owners forbids crossing that boundary while keeping his edge. Then
--   $$b_3\le d_0+f_a.$$
--   At each stable matching there is an injective assignment of its failures to $D_0\cup F_a$ at that same matching. The inverse owner formulas and the exhaustive normalized four-agent history classification from Appendix C are included as proof-support conclusions. Every valid cycle history with no repeated pair and the prescribed normalized next-owner pattern terminates in one of the four source rows.
--
--   Differences from the source:
--   - encoding: The same-matching injection justified by the complete four-name classification → A function on the actual failure subtype, with the two explicit inverse-owner formulas and all valid finite cycle histories; reason: Expresses the source injection and its exhaustive finite proof component without testing only sampled preference profiles.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 7, PDF p. 8, Lemma 10

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Local

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_10 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I) (ε : Direction) :
    (∀ hs : List (Equiv.Perm (Fin 4)), ValidHistory FourState.initial hs →
      (FourState.initial.finish hs).qualifies → (FourState.initial.finish hs).visits ∈ fourRows) ∧
    (occurrenceCounts I ε).b3 ≤ (occurrenceCounts I ε).d0 + (occurrenceCounts I ε).fa ∧
    ∀ μ : StableMatching.Matching n, I.IsStable μ →
      ∃ g : {u : Fin n // Failure I μ ε u} → Fin n,
        Function.Injective g ∧ ∀ u,
          (D0 I μ ε (g u) ∧ next I μ ε (g u) = u.val) ∨
          (Fa I μ ε (g u) ∧ owner I μ ε (next I μ ε (g u)) 2 = u.val) := by sorry

end SwitchingStable.Universal
