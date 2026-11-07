-- Prove2me | Theorems.Thm_SmolenskyAC_lemma_3
-- name    : SmolenskyAC.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:38.73469+00:00
-- url     : https://prove2.me/theorems/5e8af628-2c0a-402b-ba63-600724aebdb4
-- title:
--   Lemma 3 — $\prod_i Y_i$ with $Y_i=(h-1)X_i+1$ is $U^n_F$-complete
-- statement:
--   Let $F$ be a field, $h\in F$ with $h\ne 0$ and $h\ne 1$, and $n\ge0$. Put $Y_i=(h-1)X_i+1\in U^n_F$, the function equal to $h$ where $X_i=1$ and to $1$ where $X_i=0$. Then $\prod_{i=1}^n Y_i$ is $U^n_F$-complete: for every algebra $A\in\Omega^n_F$ and every $u\in U^n_F$,
--
--   $$\deg_A(u)\le \frac n2+\deg_A\Big(\prod_{i=1}^n Y_i\Big).$$
--
--   It is the paper's basic example of a complete element.
--
--   Differences from the source:
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: deg_A(u) ≤ n/2 + deg_A(v) → 2·deg_A(u) ≤ n + 2·deg_A(v) in ℕ; reason: the same inequality cleared of the fraction
--   - encoding: an element v^n → the one-element family indexed by Unit; reason: the definition is stated for families; same instances
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Lemma 3, p.80 (pdf 4)

import Mathlib
import Definitions.Def_SmolenskyAC_UComplete

namespace SmolenskyAC

/-- **Lemma 3** (Smolensky, STOC 1987, p.80): let `h ∈ F`, `h ≠ 0` and `h ≠ 1`. Take
`Y_i = (h − 1) X_i + 1`; then `∏_{i=1}^n Y_i` is `U^n_F`-complete. -/
theorem lemma_3 (F : Type*) [Field F] (h : F) (h0 : h ≠ 0) (h1 : h ≠ 1) (n : ℕ) :
    IsUComplete (fun _ : Unit => fun x : Cube n => ∏ i, ((h - 1) * toF (x i) + 1)) := by sorry

end SmolenskyAC
