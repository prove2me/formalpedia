-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_2
-- name    : SparseCCE.ThreePlayer.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:05:31.434638+00:00
-- url     : https://prove2.me/theorems/6feb27d4-9fea-4892-953e-54f2b56544a7
-- title:
--   Lemma 3.2 — domination by $\dim\operatorname{span}C$ laws, computable in polynomial time
-- statement:
--   (Existence) For every nonempty finite set $C$ of probability distributions on a finite set $S$, with $r=\dim\operatorname{span}C$, there are $r$ laws $c_1,\dots,c_r\in C$ with $c\le 2(c_1+\dots+c_r)$ pointwise for every $c\in C$.
--
--   (Computation) There is a polynomial-time algorithm that, given the code of a nonempty finite set of rational distributions on $\mathrm{Fin}\,n$ (listed without repetition), outputs the code of a list of exactly $r=\dim\operatorname{span}C$ laws of $C$ dominating $C$ in this sense; no bound on $r$ is assumed.
--
--   Differences from the source:
--   - encoding: the laws in C rational, given by an encoding of C → a duplicate-free list of rational vectors on Fin n coded by lawsCode (count, then encRatVec of each law); the output is the list of chosen laws in the same code; reason: a concrete binary code of the input and the output; the existence part is for real laws on any finite type
--   - encoding: computed in time polynomial in the encoding length of C → CookPvsNP.PolyTimeComputable on that code; reason: the platform notion of polynomial-time computability
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.2, p. 15; proof App. A.2, p. 28.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_Domination

namespace SparseCCE.ThreePlayer

/-- **Lemma 3.2 (Domination by few laws)**, p. 15: for a nonempty finite set `C` of probability
distributions on a finite set, with `r = dim span C`, there are `r` laws `c₁, …, c_r ∈ C` with
`c ≤ 2(c₁ + ⋯ + c_r)` for every `c ∈ C`; for rational laws, such laws are computable in time
polynomial in the encoding length of `C`, even if `r` is not bounded. -/
theorem lemma_3_2 :
    (∀ {S : Type} [Fintype S] (C : Finset (S → ℝ)), C.Nonempty → (∀ c ∈ C, IsDist c) →
      ∃ c : Fin (Module.finrank ℝ (Submodule.span ℝ (↑C : Set (S → ℝ)))) → S → ℝ,
        IsDominatingFamily C _ c) ∧
    ∃ alg : List Bool → List Bool, CookPvsNP.PolyTimeComputable alg ∧
      ∀ (n : ℕ) (l : List (Fin n → ℚ)), l ≠ [] → l.Nodup → (∀ c ∈ l, IsDist (ratLawToReal c)) →
        ∃ out : List (Fin n → ℚ), alg (lawsCode n l) = lawsCode n out ∧
          out.length = Module.finrank ℝ (Submodule.span ℝ (↑(lawSet l) : Set (Fin n → ℝ))) ∧
          IsDominatingFamily (lawSet l) out.length (fun s => ratLawToReal (out.get s)) := by sorry

end SparseCCE.ThreePlayer
