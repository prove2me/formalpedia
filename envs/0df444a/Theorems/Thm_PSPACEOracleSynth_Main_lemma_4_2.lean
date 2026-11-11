-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_4_2
-- name    : PSPACEOracleSynth.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:43.253207+00:00
-- url     : https://prove2.me/theorems/7c74d9d0-b7c5-4346-afd2-5ef05b296e99
-- title:
--   Lemma 4.2 — a finite inverse-closed set of determinant-one words over $\{H,T,T^\dagger\}$ generating a dense subgroup of $SU(2)$
-- statement:
--   There is a finite inverse-closed set $S$ of words over $\{H,T,T^\dagger\}$, each of determinant one, that generates a dense subgroup of $SU(2)$.
--
--   Since $H$ has determinant $-1$ and $T$ determinant $e^{i\pi/4}$, the condition concerns the products. Such a set is the input to the Solovay–Kitaev theorem (Fact 2.8), which then approximates every element of $SU(2)$ to precision $2^{-t}$ by words over $S$ of length polynomial in $t$.
--
--   **Formalization Note.** $S$ is a finite subset of `Matrix.specialUnitaryGroup Bool ℂ` (so each element has determinant one), closed under inverses, each element the product of a list of letters $H,T,T^\dagger$ in application order (`IsHTWord`), and the subgroup it generates is dense in the subspace topology.
--
--   Differences from the source:
--   - encoding: S a set of words, each of determinant one; dense subgroup of SU(2) → S ⊆ specialUnitaryGroup Bool ℂ finite, each element the product of a word; Dense (Subgroup.closure S); reason: a word of determinant one is an element of SU(2); same sets
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §4.2, Lemma 4.2, p. 26

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_GateSet

open QAlgorithms.Complexity

namespace PSPACEOracleSynth.Main

/-- **Lemma 4.2**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 26. There is a finite inverse-closed set `S` of words over `{H, T, T†}`, each of
determinant one, that generates a dense subgroup of `SU(2)`. -/
theorem lemma_4_2 :
    ∃ S : Set (Matrix.specialUnitaryGroup Bool ℂ),
      S.Finite ∧ (∀ W ∈ S, W⁻¹ ∈ S) ∧ (∀ W ∈ S, IsHTWord (W : Matrix Bool Bool ℂ)) ∧
      Dense ((Subgroup.closure S : Subgroup (Matrix.specialUnitaryGroup Bool ℂ)) :
        Set (Matrix.specialUnitaryGroup Bool ℂ)) := by sorry

end PSPACEOracleSynth.Main
