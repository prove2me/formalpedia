-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_corollary_2_18
-- name    : SparseLowFactors.BoundedDeg.corollary_2_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:22.709232+00:00
-- url     : https://prove2.me/theorems/35ac5e06-a2eb-4df3-b5b1-5233140c4134
-- title:
--   Corollary 2.18 — $\dim\ker\mathrm{Syl}(f,f') \ge \sum_i (e_i-1)\deg h_i$, with equality for distinct coprime irreducibles
-- statement:
--   Let $F$ be a field with $\mathrm{char}\,F=0$ or $\mathrm{char}\,F>d$, and let $f\in F[X]$ be monic, non-constant, of degree at most $d$. Suppose $f=\prod_ih_i^{e_i}$ for monic non-constant $h_i\in F[X]$. Then
--   $$\dim\ker\mathrm{Syl}(f,f')\ \ge\ \sum_i(e_i-1)\deg h_i ,$$
--   and equality holds if the $h_i$ are distinct, pairwise coprime and irreducible (and the exponents are positive).
--
--   The equality case computes the kernel dimension from the irreducible factorization; Lemma 3.2 compares it before and after substituting a point.
--
--   **Formalization Note** The factors are indexed by a finite type; the sum is computed in $\mathbb Z$. $\mathrm{Syl}(f,f')$ uses the degrees of $f$ and $f'$ as in Definition 2.15.
--
--   Differences from the source:
--   - reading: equality "if the h_i are distinct pairwise coprime irreducible polynomials" → equality under that hypothesis and e_i ≥ 1 for all i; reason: the intended statement (the proof works with a factorization, whose exponents are positive); as printed, with some e_i = 0 the sum contains −deg h_i and the equality fails (finding I4); the inequality is stated for all e_i ≥ 0, as printed
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 20, Corollary 2.18

import Mathlib
import Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester

open Polynomial

namespace SparseLowFactors.BoundedDeg

theorem corollary_2_18 (F : Type) [Field F] (d : ℕ) (hchar : ringChar F = 0 ∨ d < ringChar F)
    (f : Polynomial F) (hmon : f.Monic) (hnc : 0 < f.natDegree) (hd : f.natDegree ≤ d)
    {ι : Type} [Fintype ι] (h : ι → Polynomial F) (e : ι → ℕ)
    (hh : ∀ i, (h i).Monic ∧ 0 < (h i).natDegree) (hf : f = ∏ i, h i ^ e i) :
    (∑ i, ((e i : ℤ) - 1) * ((h i).natDegree : ℤ) ≤
        (Module.finrank F (LinearMap.ker (Matrix.toLin' (sylv f (derivative f)))) : ℤ)) ∧
    ((Function.Injective h ∧ Pairwise (fun i j => IsCoprime (h i) (h j)) ∧
        (∀ i, Irreducible (h i)) ∧ (∀ i, 1 ≤ e i)) →
      (Module.finrank F (LinearMap.ker (Matrix.toLin' (sylv f (derivative f)))) : ℤ) =
        ∑ i, ((e i : ℤ) - 1) * ((h i).natDegree : ℤ)) := by sorry

end SparseLowFactors.BoundedDeg
