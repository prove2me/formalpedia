-- Prove2me | Theorems.Thm_PlunneckeType_Abelian_theorem_3_1_step
-- name    : PlunneckeType.Abelian.theorem_3_1_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:12.984844+00:00
-- url     : https://prove2.me/theorems/a9860ff9-3184-459b-b726-4ede201c7743
-- title:
--   Proof of Theorem 3.1, inductive step — $|X + hB| \le \alpha|X + (h-1)B|$ for a minimal-growth $X \subseteq A$
-- statement:
--   Let $G$ be an abelian group, written additively, and let $A$, $B$ be finite subsets of $G$. For $h \ge 0$ write $hB = B + \cdots + B$ ($h$ summands) for the iterated sumset, with $0B = \{0\}$. Let $\alpha$ be a real number with
--   $$|A + B| \le \alpha |A|,$$
--   and let $X \subseteq A$ be a nonempty subset of minimal growth under addition of $B$:
--   $$\frac{|X + B|}{|X|} \le \frac{|Z + B|}{|Z|} \quad \text{for every nonempty } Z \subseteq A.$$
--   Then for every integer $h \ge 1$
--   $$|X + hB| \le \alpha\, |X + (h-1)B|.$$
--
--   This is the inductive step in the proof of Theorem 3.1: applied for $h = 1, 2, \dots$ it gives $|X + hB| \le \alpha^h |X|$ with the same $X$ for every $h$.
--
--   **Formalization Note** The minimality is stated cross-multiplied, $|X + B|\,|Z| \le |Z + B|\,|X|$, which avoids division. $hB$ is the $h$-fold sumset `h • B` (not the dilate $\{hb\}$), and $h - 1$ is natural-number subtraction, guarded by the hypothesis $h \ge 1$.
-- source:
--   G. Petridis, New proofs of Plünnecke-type estimates for product sets in groups, arXiv:1101.3507v3, p. 7, proof of Theorem 3.1 (the display |X + hB| = |(h−1)B + X + B| ≤ α|X + (h−1)B|)

import Mathlib
open scoped Pointwise
open Finset

namespace PlunneckeType.Abelian

/-- Petridis, arXiv:1101.3507v3, p. 7, proof of Theorem 3.1 (the inductive step). Let `A, B` be
finite sets in an abelian group with `|A + B| ≤ α|A|`, and let `X ⊆ A` be nonempty and minimise
`|Z + B|/|Z|` over the nonempty `Z ⊆ A` (stated cross-multiplied). Then for every `h ≥ 1`,
`|X + hB| ≤ α |X + (h - 1)B|`, where `hB = h • B` is the `h`-fold sumset. -/
theorem theorem_3_1_step {G : Type*} [AddCommGroup G] [DecidableEq G] (A B X : Finset G) (α : ℝ)
    (hAB : (#(A + B) : ℝ) ≤ α * #A)
    (hXA : X ⊆ A) (hX : X.Nonempty)
    (hmin : ∀ Z ⊆ A, Z.Nonempty → (#(X + B) : ℝ) * #Z ≤ #(Z + B) * #X)
    (h : ℕ) (hh : 1 ≤ h) :
    (#(X + h • B) : ℝ) ≤ α * #(X + (h - 1) • B) := by sorry

end PlunneckeType.Abelian
