-- Prove2me | Theorems.Thm_SmolenskyAC_lemma_4
-- name    : SmolenskyAC.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:37.859976+00:00
-- url     : https://prove2.me/theorems/33baf5c8-fe86-4085-8ced-c0c8fa51ddf8
-- title:
--   Lemma 4 — degree $o(\sqrt n)$ on a complete set forces dimension at most $2^{n-1}+o(2^n)$
-- statement:
--   Let $F$ be a field. For each $n$ let $v^n_1,\dots,v^n_s$ (finitely many, $s$ depending on $n$) be a $U^n_F$-complete family and $E_n\subseteq D^n$, and suppose that every $v^n_i$ has degree at most $d(n)$ in $A^n=U^n_F/I_{E_n}$ with $d(n)=o(\sqrt n)$. Then there is $e(n)=o(2^n)$ with
--
--   $$\dim A^n=|D^n\setminus E_n|\le 2^{n-1}+e(n)\qquad\text{for all } n.$$
--
--   It turns completeness into a bound on the size of any algebra in which the complete set is cheap.
--
--   Differences from the source:
--   - encoding: a collection of circuits C^n, one per input length, with o(·) in n (Remark, p.78) → a family indexed by every n; the o(·) witnesses are chosen after the family; reason: the Remark's meaning of the superscript n
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: the degree of a set is o(√n) → every element has degree at most d(n), d = o(√n); reason: the degree of a set is its largest degree
--   - encoding: 2^(n−1) → 2^n / 2 in ℝ; reason: no truncated subtraction at n = 0
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Lemma 4, p.80 (pdf 4)

import Mathlib
import Definitions.Def_SmolenskyAC_UComplete

open Asymptotics Filter

namespace SmolenskyAC

/-- **Lemma 4** (Smolensky, STOC 1987, p.80): if an element `v^n` (or a set `v^n_1, …, v^n_s`) is
`U^n_F`-complete, and in some algebra `A^n ∈ Ω^n_F` its degree is `o(√n)`, then the dimension of
`A^n` is at most `2^{n−1} + o(2^n)`.

**Formalization Note.** Families indexed by `n` (Remark, p.78); the algebra `A^n` is the erased
set `E n` and its dimension is the number of assignments outside `E n`. The degree of a set is the
largest degree of its elements. `2^{n−1}` is `2^n / 2` in `ℝ`. The error term `e` is chosen after
the families. -/
theorem lemma_4 (F : Type*) [Field F] {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (v : ∀ n, ι n → Cube n → F) (hv : ∀ n, IsUComplete (v n))
    (E : ∀ n, Finset (Cube n)) (d : ℕ → ℝ) (hd : d =o[atTop] fun n : ℕ => Real.sqrt n)
    (hdeg : ∀ n (i : ι n), (degOff (E n) (v n i) : ℝ) ≤ d n) :
    ∃ e : ℕ → ℝ, e =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) ∧
      ∀ n, ((E n)ᶜ.card : ℝ) ≤ (2 : ℝ) ^ n / 2 + e n := by sorry

end SmolenskyAC
