-- Prove2me | Theorems.Thm_QGraphColl_lemma_3_2
-- name    : QGraphColl.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:43.192832+00:00
-- url     : https://prove2.me/theorems/0d3697d0-c5eb-402b-a947-093a9b7787d4
-- title:
--   Lemma 3.2 — thresholding: $\mathrm{vol}(G[P],x)\le n\tau+\sqrt{nr}$ and a cheap outside cover
-- statement:
--   Let $G$ be a graph on $V$ with $n=|V|$, $x$ an input with marked set $M$, $S\subseteq V$, $\tau>0$,
--   $$r=\sum_u\big(\ell_u(S)-\ell_u(M)\big)^2,\qquad P=\{u:\ \ell_u(S)\le\tau\}.$$
--   Then:
--
--   1. $\mathrm{vol}(G[P],x)\le n\tau+\sqrt{nr}$;
--   2. on a negative input, $|M\setminus P|\le r/\tau^2$;
--   3. if the input is negative and every degree is at most $d$, then $V\setminus P$ is a vertex cover of the edges outside $G[P]$, and its marked volume in those edges is at most $dr/\tau^2$.
--
--   Thresholding the estimated counts splits the graph into a part of small marked volume and a part with a cover of small marked volume, both cheap to test with Lemma 2.7.
--
--   Differences from the source:
--   - encoding: G[P] and 'the edges outside G[P] have cover V(G) \ P of marked volume at most dr/τ²' → restrict G P on the same labels; IsCover (G \ restrict G P) (V \ P) and vol(G \ restrict G P, V \ P, x) ≤ dr/τ²; reason: edge deletions retain labels (p.12); the marked volume of a cover of an edge set is Definition 2.1 for that edge set
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma 3.2, p.15

import Mathlib
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict

namespace QGraphColl

/-- **Lemma 3.2** (Thresholding; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.15). Let `S ⊆ V(G)`, let
`r = ∑_u (ℓ_u(S) − ℓ_u(M))²`, and let `P = {u : ℓ_u(S) ≤ τ}` for `τ > 0`. Then
`vol(G[P], x) ≤ nτ + √(nr)`. On a negative input, `|M \ P| ≤ r/τ²`. If the input is negative and
the maximum degree is at most `d`, the edges outside `G[P]` have cover `V(G) \ P` of marked volume
at most `dr/τ²`.

**Formalization Note.** `n = |V|`. `G[P]` is `restrict G P` on the same labels; the edges outside
`G[P]` are the graph `G \ restrict G P`, and the marked volume of the cover `V \ P` is taken with
degrees in that edge set (Definition 2.1 applied to it). The cover property is part of the claim. -/
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V → Bool)
    (S : Finset V) (τ : ℝ) (hτ : 0 < τ) :
    let r : ℝ := ∑ u, ((ell G S u : ℝ) - (ell G (marked x) u : ℝ)) ^ 2
    let P : Finset V := Finset.univ.filter fun u => (ell G S u : ℝ) ≤ τ
    (vol (restrict G P) Finset.univ x : ℝ) ≤
        (Fintype.card V : ℝ) * τ + Real.sqrt ((Fintype.card V : ℝ) * r) ∧
      (gc G x = false → ((marked x \ P).card : ℝ) ≤ r / τ ^ 2) ∧
      (∀ d : ℝ, gc G x = false → (∀ v, (deg G v : ℝ) ≤ d) →
        IsCover (G \ restrict G P) (Finset.univ \ P) ∧
        (vol (G \ restrict G P) (Finset.univ \ P) x : ℝ) ≤ d * r / τ ^ 2) := by sorry

end QGraphColl
