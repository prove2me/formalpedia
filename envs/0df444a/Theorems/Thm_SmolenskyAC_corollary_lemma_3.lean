-- Prove2me | Theorems.Thm_SmolenskyAC_corollary_lemma_3
-- name    : SmolenskyAC.corollary_lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:22.332143+00:00
-- url     : https://prove2.me/theorems/79fea11a-238a-4cd2-b2ff-26cf2b7ba5b2
-- title:
--   Corollary to Lemma 3 — with a $q$-th root of unity, $\{\mathrm{MOD}_{s,q}\}_{s<q}$ is $U^n_F$-complete
-- statement:
--   Let $F$ be a field, $q\ge 1$, and suppose $F$ contains a $q$-th root of unity, i.e. an $a\in F$ with $a\ne 1$ and $a^q=1$ (not necessarily primitive). Then for every $n$ the set
--
--   $$\{\mathrm{MOD}_{0,q}(X_1,\dots,X_n),\ \dots,\ \mathrm{MOD}_{q-1,q}(X_1,\dots,X_n)\}$$
--
--   is $U^n_F$-complete, each $\mathrm{MOD}_{s,q}$ read in $F$ as a $0/1$-valued function.
--
--   With Theorem 1 this makes the $\mathrm{MOD}_{s,q}$ functions hard for small circuits whose gates are cheap in degree over $F$.
--
--   Differences from the source:
--   - encoding: an algebra A = U^n_F / I in Ω^n_F, its dimension and deg_A → an erased set E ⊆ D^n (I = functions vanishing outside E), dimension |D^n ∖ E|, degOff E; reason: every ideal of U^n_F is of this form (p.79); same instances
--   - encoding: q-th root of unity, MOD_{s,q} for s = 0, …, q − 1 → 0 < q; reason: modulus 0 and the index range 0, …, −1 are undefined
--   - encoding: MOD_{s,q} as an element of U^n_F → its values 0/1 read in F; reason: the page identifies False with 0_F and Truth with 1_F
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Corollary (to Lemma 3), p.80 (pdf 4); Definition of q-th root of unity, p.80

import Mathlib
import Definitions.Def_SmolenskyAC_UComplete

namespace SmolenskyAC

/-- **Corollary to Lemma 3** (Smolensky, STOC 1987, p.80): if `F` contains a `q`-th root of unity
(an `a ∈ F` with `a ≠ 1` and `a^q = 1`, Definition, p.80; not necessarily primitive), then the
set `{MOD_{0,q}(X_1, …, X_n), …, MOD_{q−1,q}(X_1, …, X_n)}` is `U^n_F`-complete.

**Formalization Note.** Each `MOD_{s,q}` is read in `F` through `False ↦ 0`, `True ↦ 1`. `q > 0`
excludes the modulus `0`, for which `MOD_{s,0}` and the index range `0, …, q − 1` are undefined. -/
theorem corollary_lemma_3 (F : Type*) [Field F] (q : ℕ) (hq : 0 < q) (a : F) (ha : a ≠ 1)
    (haq : a ^ q = 1) (n : ℕ) :
    IsUComplete (fun s : Fin q => fun x : Cube n => (toF (MODs s.val q n x) : F)) := by sorry

end SmolenskyAC
