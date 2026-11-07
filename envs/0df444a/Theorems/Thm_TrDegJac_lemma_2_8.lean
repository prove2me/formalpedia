-- Prove2me | Theorems.Thm_TrDegJac_lemma_2_8
-- name    : TrDegJac.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:43.721886+00:00
-- url     : https://prove2.me/theorems/0674f4cb-9c9b-4736-b72c-292eaf0accbd
-- title:
--   Lemma 2.8 — exchange lemma for transcendence bases
-- statement:
--   Let $B,S\subseteq\mathbb F[x_1,\dots,x_n]$ be finite sets, where $B$ is a transcendence base of $\mathbb F(x)$ over $\mathbb F$ (a maximally algebraically independent subset of $\mathbb F[x]$) and $S$ is algebraically independent over $\mathbb F$. If $|S|<|B|$, then there is $q\in B$ with $q\notin S$ such that
--   $$
--   S\cup\{q\}\ \text{is algebraically independent over }\mathbb F.
--   $$
--
--   The proof of Theorem 4.12 applies it repeatedly to complete a maximal subfamily $g$ to $n$ independent polynomials by adding coordinate variables.
--
--   Differences from the source:
--   - reading: there exists some f ∈ B such that S ∪ {f} is algebraically independent → there exists q ∈ B with q ∉ S such that S ∪ {q} is algebraically independent; reason: as printed any q ∈ B ∩ S satisfies the conclusion and the lemma says nothing; the proof of Theorem 4.12 (p.29) uses it to enlarge S, which is the stronger reading
--   - encoding: B, S ⊆ F[x] finite, |S| < |B| → sets with Set.Finite hypotheses and Set.ncard; reason: the same sets and sizes
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 2.8, p.8

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 2.8 (exchange lemma)** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.8:
"If B, S ⊆ F[x] are finite, B is a transcendence base, S is algebraically independent, and
|S| < |B|, then there exists some f ∈ B such that S ∪ {f} is algebraically independent."

**Formalization Note.** `B` and `S` are sets of polynomials with `Set.Finite` hypotheses, and `|·|` is `Set.ncard`. "Transcendence
base" (Definition 2.6) is Mathlib's `IsTranscendenceBasis` over `F` for the inclusion of `B` into
`F[x]`. The new element `q` is required to lie outside `S`: as printed the lemma is satisfied by any
`q ∈ B ∩ S`, while the proof of Theorem 4.12 (p.29) uses it to enlarge `S` by a new element. -/
theorem lemma_2_8 {F : Type*} [Field F] {n : ℕ} (B S : Set (MvPolynomial (Fin n) F))
    (hBfin : B.Finite) (hSfin : S.Finite)
    (hB : IsTranscendenceBasis F ((↑) : B → MvPolynomial (Fin n) F))
    (hS : AlgebraicIndependent F ((↑) : S → MvPolynomial (Fin n) F))
    (hcard : S.ncard < B.ncard) :
    ∃ q ∈ B, q ∉ S ∧
      AlgebraicIndependent F
        ((↑) : ↥(insert q S : Set (MvPolynomial (Fin n) F)) → MvPolynomial (Fin n) F) := by sorry

end TrDegJac
