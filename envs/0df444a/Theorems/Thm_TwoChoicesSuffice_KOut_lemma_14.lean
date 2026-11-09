-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_14
-- name    : TwoChoicesSuffice.KOut.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:06.916867+00:00
-- url     : https://prove2.me/theorems/a7a5d704-991a-4388-8a9b-deece3b7c8c8
-- title:
--   Lemma 14 — number of proper colourings of a first-choice graph
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices without isolated vertices, and let $\sigma$ be a two-choice outcome, so the first choice $s_1(v)$ of every vertex is a neighbour of $v$. View $H^1_G(\sigma)$ as the functional graph of $v\mapsto s_1(v)$, and let $\ell(Q)$ be the length of a directed cycle $Q$, two opposite directed edges forming a directed cycle of length two. For every integer $q\ge2$,
--   $$
--   Z_q\bigl(H^1_G(\sigma)\bigr)=(q-1)^n\prod_{\text{directed cycles }Q\text{ in }H^1_G(\sigma)}\left(1+\frac{(-1)^{\ell(Q)}}{(q-1)^{\ell(Q)-1}}\right),
--   $$
--   each directed cycle counted once.
--
--   This exact count is used to compare the probabilities of a marked set before and after a switching in the two-out case.
--
--   **Formalization Note** Directed cycles are the periodic orbits of `fun v => σ v 0`, their length the orbit size; the empty product is $1$.
--
--   Differences from the source:
--   - encoding: no isolated vertices (standing assumption of §3) → explicit hypothesis that every vertex has a G-neighbour, and σ an outcome of the two-out law; reason: the source's working domain made explicit; the identity is about genuine first-choice maps
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 14, printed p. 18, PDF p. 19; proof in Appendix A, PDF pp. 26–27

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Coloring

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 14 (PDF p. 19, printed p. 18; proof Appendix A, PDF pp. 26–27). Let `G` be a
simple graph without isolated vertices and `σ` an ordered two-choice outcome. Viewing the
first-choice graph `H^1_G(σ)` as the functional graph of `v ↦ s₁(v)`, for every integer
`q ≥ 2` its number of proper `q`-colourings is
`Z_q(H^1_G(σ)) = (q-1)^n ∏_Q (1 + (-1)^{ℓ(Q)} / (q-1)^{ℓ(Q)-1})`, the product over the
directed cycles `Q` of the first-choice map (each once, two opposite arcs forming a cycle of
length two), `ℓ(Q)` its length. -/
theorem lemma_14 {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (σ : V → Fin 2 → V) (hσ : σ ∈ outcomes G 2) (q : ℕ) (hq : 2 ≤ q) :
    (numColorings q (prefixGraph G σ 1) : ℝ) =
      ((q : ℝ) - 1) ^ Fintype.card V *
        ∏ Q ∈ directedCycles (fun v => σ v 0),
          (1 + (-1 : ℝ) ^ Q.card / ((q : ℝ) - 1) ^ (Q.card - 1)) := by sorry

end TwoChoicesSuffice.KOut
