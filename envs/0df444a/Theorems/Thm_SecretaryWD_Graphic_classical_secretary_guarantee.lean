-- Prove2me | Theorems.Thm_SecretaryWD_Graphic_classical_secretary_guarantee
-- name    : SecretaryWD.Graphic.classical_secretary_guarantee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:27.38296+00:00
-- url     : https://prove2.me/theorems/da01a9b7-b6b7-4b12-8a47-f431f2abadfa
-- title:
--   The classical secretary rule selects the maximum with probability at least 1/e
-- statement:
--   Let $m\ge 1$ and let $v_0,\dots,v_{m-1}$ be real values, ranked by the tie-break order (larger value first, and among equal values the smaller index first). Let the $m$ elements arrive in a uniformly random order. The classical secretary rule observes the first $\lfloor m/e\rfloor$ arrivals and then selects the first arrival that ranks above every earlier arrival. Then
--   $$\Pr_\pi\big[\text{the rule selects the top-ranked element}\big]\;\ge\;\frac1e .$$
--
--   This is the guarantee behind the paper's remark that the classical secretary algorithm is $e$-competitive. Theorem 5.4 applies it to each part of a partition matroid.
--
--   **Formalization Note.** The probability is the number of arrival orders $\sigma$ for which the selected position $t$ carries the top-ranked element, divided by $m!$. The arrival order is $\sigma$ (time $\mapsto$ element), and the keys handed to the rule are the tie-break keys of $\sigma(0),\sigma(1),\dots$. For $m=1,2$ the sample is empty and the probability is $1$ and $\tfrac12$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 4, Section 2 (the classical secretary algorithm is e-competitive)

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

namespace SecretaryWD.Graphic
theorem classical_secretary_guarantee (m : ℕ) (hm : 1 ≤ m) (v : Fin m → ℝ) :
    1 / Real.exp 1 ≤
      (1 / (m.factorial : ℝ)) *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, SecretaryWD.DiscUpper.classicalSecretary m (fun s => SecretaryWD.DiscUpper.tieKey v (σ s)) = some t ∧
              ∀ e : Fin m, SecretaryWD.DiscUpper.tieKey v e ≤ SecretaryWD.DiscUpper.tieKey v (σ t)).card : ℝ) := by sorry
end SecretaryWD.Graphic
