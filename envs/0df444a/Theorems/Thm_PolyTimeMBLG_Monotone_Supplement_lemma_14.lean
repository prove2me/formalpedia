-- Prove2me | Theorems.Thm_PolyTimeMBLG_Monotone_Supplement_lemma_14
-- name    : PolyTimeMBLG.Monotone.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:34:40.027246+00:00
-- url     : https://prove2.me/theorems/eaaa7d0a-6a42-4f4d-a8f8-bc441eb419da
-- title:
--   Lemma 14 — if 3-CNFs are polynomial-time MBLG, polynomial-size circuits are polynomial-time MBLG in the open regime
-- statement:
--   Suppose the family of 3-CNFs (conjunctions of any number of disjunctions of 3 literals over $x_1,\dots,x_n$) is polynomial-time MBLG in the sense of Definition 6. Then for every polynomial $p$, the family of $p(n)$-size circuits is polynomial-time MBLG in the open regime: there are a polynomial $e$ and one open-regime generator $G$, computed by one Turing machine in time polynomial in the length of its input $(C,1^n,x^1\cdots x^i)$, such that for every $n\ge1$, every circuit $C$ on $n$ inputs with at most $p(n)$ gates and every enumeration $x^1,\dots,x^{|C^{-1}(1)|}$ of $C^{-1}(1)$,
--   $$\#\Bigl\{\,i\in\{0,\dots,|C^{-1}(1)|-1\}\ :\ G(C,1^n,x^1\cdots x^i)\notin C^{-1}(1)\setminus\{x^1,\dots,x^i\}\Bigr\}\ \le\ e(n).$$
--
--   In the open regime the language is known, so only the task of producing new members remains. The lemma is the second step of the proof of Theorem 3.
--
--   **Formalization Note** The generator and the mistake polynomial may depend on $p$. Circuits are fan-in-two AND/OR and NOT circuits with size the number of gates (the published `QCSepTotal.Circuit`), and the circuit is part of the encoded input.
--
--   Differences from the source:
--   - reading: "3CNF" → a conjunction of any finite number $m\ge0$ of clauses of at most 3 literals (variable indices may coincide); reason: the family of Lemma 13, as used in the proof on p. 9, where the Circuit-SAT to 3-SAT reduction produces clauses with fewer than three literals; for $n\ge3$ it equals the family of conjunctions of 3-literal clauses on distinct variables.
--   - encoding: "for any polynomial $p(n)$" → every $p$ with natural coefficients; reason: circuit sizes are natural numbers and every real polynomial is bounded on $\mathbb N$ by one with natural coefficients, while a generator for a larger size cap also serves a smaller one, so both quantifications give the same statement.
--   - encoding: the paper's unspecified circuit model → fan-in-two AND/OR gates and NOT gates, size = number of gates, no constant gates; reason: the paper fixes no model, and standard models are polynomially related, so "for any polynomial $p$" means the same.
--   - encoding: polynomial-time MBLG in the open regime → a polynomial-time machine on the encoded input (circuit code, then $1^n$ and the words), polynomial mistake bound, without the size condition of Definition 6; reason: the encoded input length is polynomial in $n(i+1)$ when the size is at most $p(n)$, and the number of such circuits is at most $2^{\mathrm{poly}(n)}$, so the size condition always holds.
--   - encoding: the hypothesis "3CNFs polynomial-time MBLG" → the base mission's `IsPolyTimeMBLG`; reason: the published definition of Definition 6.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Lemma 14, its proof and the preceding paragraph defining the open regime, p. 9; Definitions 5–6, p. 5. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_Clauses
import Definitions.Def_PolyTimeMBLG_Monotone_Supplement_OpenRegime

namespace PolyTimeMBLG.Monotone.Supplement

/-- Lemma 14, p. 9: if the family of 3-CNFs is polynomial-time MBLG, then for every polynomial
`p`, the family of `p(n)`-size circuits is polynomial-time MBLG in the open regime. -/
theorem lemma_14 (h : IsPolyTimeMBLG cnf3Family) (p : Polynomial ℕ) :
    IsOpenPolyTimeMBLG p := by sorry

end PolyTimeMBLG.Monotone.Supplement
