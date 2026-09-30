-- Prove2me | Theorems.Thm_PermLimits_Cauchy_convergences_equivalent
-- name    : PermLimits.Cauchy.convergences_equivalent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:25:08.548992+00:00
-- url     : https://prove2.me/theorems/02198ea6-5be7-4261-b8a0-011fd77a9391
-- title:
--   Lemma 5.3: $Z_n\Rightarrow Z\iff Z_n\xrightarrow{\square}Z\iff Z_n\xrightarrow{t}Z$
-- statement:
--   Let $Z,Z_1,Z_2,\dots$ be limit permutations. The three notions of convergence of Definition 5.2 are equivalent:
--   $$Z_n\Rightarrow Z\iff Z_n\xrightarrow{\square}Z\iff Z_n\xrightarrow{t}Z .$$
--
--   Weak convergence of the associated random points, convergence in rectangular distance, and convergence of all pattern densities are therefore one notion on $\mathcal Z$. Combined with compactness of the space of laws on the square, this is the engine of the existence proof.
--
--   **Formalization Note** The chain of equivalences is stated as the conjunction of two equivalences.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 16, Definition 5.2 and Lemma 5.3

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Cauchy

open unitInterval

/-- **Lemma 5.3** (Hoppen et al., *Limits of permutation sequences*, arXiv:1103.5844v2, p. 16).
Let `Z, Z₁, Z₂, …` be limit permutations. The three notions of convergence of Definition 5.2 are
equivalent: `Z_n ⇒ Z ⟺ Z_n →□ Z ⟺ Z_n →ᵗ Z`.

**Formalization Note.** The chain of equivalences is the conjunction of two `↔`. -/
theorem convergences_equivalent (Zs : ℕ → I → I → ℝ) (Z : I → I → ℝ)
    (hZs : ∀ n, IsLimitPerm (Zs n)) (hZ : IsLimitPerm Z) :
    (WeakConv Zs Z ↔ RectConv Zs Z) ∧ (RectConv Zs Z ↔ DensityConv Zs Z) := by sorry

end PermLimits.Cauchy
