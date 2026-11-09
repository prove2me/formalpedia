-- Prove2me | Theorems.Thm_TermCycDich_excludes_planar_iff_bounded_bidim
-- name    : TermCycDich.excludes_planar_iff_bounded_bidim
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:32.086041+00:00
-- url     : https://prove2.me/theorems/1da65e77-bd99-46f0-9c48-ac21467df9f5
-- title:
--   Proof of Theorem 1.1 — excluding an annotated planar graph ⇔ bounded bidimensionality
-- statement:
--   Let $\mathcal C$ be a red-minor-closed class of annotated graphs. Then $\mathcal C$ does not contain all annotated planar graphs if and only if there is a constant $c$ such that
--
--   $$
--   \mathrm{bidim}(G,R)\le c\qquad\text{for all }(G,R)\in\mathcal C.
--   $$
--
--   This equivalence turns the hypothesis of the tractable half of Theorem 1.1 into the parameter bound that Theorem 8.1 needs.
--
--   Differences from the source:
--   - encoding: an annotated graph (G, R) with G finite and simple → AnnotatedGraph: vertex set Fin n, red set a Finset (Fin n), input code encode = n in unary, the n² adjacency bits, the n red bits; reason: the paper fixes no encoding; red-minor-closed classes are closed under isomorphism and any standard encoding is polynomially equivalent
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), proof of Theorem 1.1, p.67 (PDF 69)

import Mathlib
import Definitions.Def_TermCycDich_IsRedMinorClosed
import Definitions.Def_TermCycDich_IsAnnotatedPlanar
import Definitions.Def_TermCycDich_bidim

namespace TermCycDich

/-- **A red-minor-closed class excludes some annotated planar graph if and only if its
bidimensionality is bounded.**

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), proof of Theorem 1.1, p.67 (PDF 69): "assume that C does not contain all annotated planar
graphs. We will show that this is equivalent to the fact that there exists some constant c such
that all annotated graphs in C have bidimensionality at most c."

**Formalization Note** Both directions, for every red-minor-closed class. -/
theorem excludes_planar_iff_bounded_bidim (C : Set AnnotatedGraph) (hC : IsRedMinorClosed C) :
    (¬ ∀ x, IsAnnotatedPlanar x → x ∈ C) ↔
      ∃ c : ℕ, ∀ x ∈ C, bidim x.G (↑x.R : Set (Fin x.n)) ≤ c := by sorry

end TermCycDich
