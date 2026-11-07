-- Prove2me | Theorems.Thm_TrDegJac_lemma_2_7
-- name    : TrDegJac.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:41.180225+00:00
-- url     : https://prove2.me/theorems/87aa7713-aa1c-4aa2-b3f4-499227c59677
-- title:
--   Lemma 2.7 — transcendence bases have size $n$; maximal subfamilies have size $\operatorname{tr-deg}$
-- statement:
--   Let $\mathbb F$ be a field.
--
--   1. Every set $S\subseteq\mathbb F[x_1,\dots,x_n]$ that is maximally algebraically independent over $\mathbb F$ (a transcendence base of $\mathbb F(x)$ over $\mathbb F$) has exactly $n$ elements.
--   2. For every family $f_1,\dots,f_m\in\mathbb F[x_1,\dots,x_n]$, every maximally algebraically independent subfamily of $f$ has exactly $\operatorname{tr-deg}_{\mathbb F}(f)$ members.
--
--   The second part is what makes Definition 2.5 well posed, and it lets Theorem 4.12 use any maximal subfamily.
--
--   Differences from the source:
--   - encoding: a transcendence base is a maximally algebraically independent set S ⊆ F[x] → Mathlib's IsTranscendenceBasis for the inclusion of S into F[x], size as Set.encard; reason: the same maximality among subsets of F[x]; encard = n also says S is finite
--   - reading: all maximally algebraically independent subsets of f have the same size → every maximal index set S has S.card = trDeg f; reason: Definition 2.5 defines tr-deg as the size of the maximal subsets, so the common size is tr-deg; trDeg is the maximum size, which is the stronger statement
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 2.7, p.8 (with Definition 2.6, p.8)

import Mathlib
import Definitions.Def_TrDegJac_IsMaxAlgIndep
import Definitions.Def_TrDegJac_trDeg

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 2.7** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.8:
"All transcendence bases of F(x₁, …, x_n) over F have size n. For f₁, …, f_m ∈ F[x], if
tr-deg_F(f) = r, then all maximally algebraically independent subsets of f have the same size."

(a) Every set `S ⊆ F[x₁, …, x_n]` that is maximally algebraically independent (Definition 2.6, p.8)
has exactly `n` elements. (b) Every maximally algebraically independent subfamily of a family `f`
has `tr-deg_F(f)` elements.

**Formalization Note.** Definition 2.6 ("a set S ⊆ F[x] that is maximally algebraically
independent") is Mathlib's `IsTranscendenceBasis F ((↑) : S → MvPolynomial (Fin n) F)`, maximality
among subsets of `F[x]`. "Size" in (a) is `Set.encard`, so the clause also says `S` is finite. In
(b) "the same size" is stated as the value `trDeg f`, the maximum size of an independent
subfamily. -/
theorem lemma_2_7 {F : Type*} [Field F] {n : ℕ} :
    (∀ S : Set (MvPolynomial (Fin n) F),
        IsTranscendenceBasis F ((↑) : S → MvPolynomial (Fin n) F) → S.encard = n) ∧
      ∀ (m : ℕ) (f : Fin m → MvPolynomial (Fin n) F) (S : Finset (Fin m)),
        IsMaxAlgIndep f S → S.card = trDeg f := by sorry

end TrDegJac
