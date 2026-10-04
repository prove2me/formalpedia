-- Prove2me | Theorems.Thm_SecretaryWD_DiscUpper_classical_secretary_guarantee
-- name    : SecretaryWD.DiscUpper.classical_secretary_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:36:59.519009+00:00
-- url     : https://prove2.me/theorems/eabfc581-d01d-43b0-8911-89b2774d06c4
-- title:
--   §2 — the classical secretary rule selects the maximum with probability at least $1/e$
-- statement:
--   Let $m\ge 1$ and let $v(0),\dots,v(m-1)$ be arbitrary real values of $m$ elements, ranked by the tie-break order (larger value first, smaller index on equal values). Let the elements arrive in a uniformly random order $\sigma$ and run the classical secretary rule on their keys: observe the first $\lfloor m/e\rfloor$ arrivals, then select the first arrival ranking above all earlier ones. Then
--   $$\Pr_\sigma\bigl[\text{the rule selects the top-ranked element}\bigr]\;\ge\;\frac1e .$$
--
--   This is the guarantee behind the paper's statement that the classical secretary algorithm is $e$-competitive; Theorem 4.4 applies it to the arrivals in one discount class.
--
--   **Formalization Note.** The probability is the fraction of the $m!$ orders $\sigma$ for which the rule returns a position $t$ whose element $\sigma(t)$ is the maximum of the tie-break order. Because the tie-break order is strict and total, no distinctness of values is assumed.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 4, Section 2 ("It is well-known that the following algorithm is e-competitive for the classical secretary problem")

import Mathlib
import Definitions.Def_SecretaryWD_DiscUpper_ClassicalSecretary

namespace SecretaryWD.DiscUpper
theorem classical_secretary_guarantee (m : ℕ) (hm : 1 ≤ m) (v : Fin m → ℝ) :
    1 / Real.exp 1 ≤
      (1 / (m.factorial : ℝ)) *
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin m) =>
            ∃ t : Fin m, classicalSecretary m (fun s => tieKey v (σ s)) = some t ∧
              ∀ e : Fin m, tieKey v e ≤ tieKey v (σ t)).card : ℝ) := by sorry
end SecretaryWD.DiscUpper
