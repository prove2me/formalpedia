-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_6_physical_lifting
-- name    : PoSUndirected.lemma_A_6_physical_lifting
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:37.944125+00:00
-- url     : https://prove2.me/theorems/3524f70a-c407-48d1-8583-ad8ca9635204
-- title:
--   Lemma A.6 — physical lifting of a route change by a walk, with its gain bound
-- statement:
--   Consider a network design game on a finite loopless multigraph with positive edge costs, a profile $A$, and a player $i$ with current path $P=A_i$ and old loads $n_e=\ell_e(A)$. Give every edge the unilateral price
--   $$
--   \pi_P(e)=\begin{cases}c_e/n_e,&e\in P,\\ c_e/(n_e+1),&e\notin P.\end{cases}
--   $$
--   For every $s_i$–$t_i$ walk $W$ there is a simple $s_i$–$t_i$ path $Q$ with $E(Q)\subseteq E(W)$ such that, with $R_{\rm old}=P\cap E(W)$,
--   $$
--   c_i(Q,P_{-i})\le\sum_{e\in R_{\rm old}}\pi_P(e)+\sum_{e\in E(W)\setminus P}\pi_P(e),
--   $$
--   and consequently the gain of the move is at least the abandoned payment minus the new payment:
--   $$
--   c_i(P)-c_i(Q,P_{-i})\ \ge\ \sum_{e\in P\setminus E(W)}\frac{c_e}{n_e}-\sum_{e\in E(W)\setminus P}\frac{c_e}{n_e+1}.
--   $$
--
--   This is how every deviation of the local comparison is turned into an actual legal unilateral move: retained pieces cancel exactly, and entered edges are priced at their joining share.
--
--   Differences from the source:
--   - reading: the printed statement ("has the gain lower bounds used below") → the inequality displayed in its proof and the gain bound $A_0-J_0$ derived from it there; reason: the printed statement points forward and its mathematical content is the displayed inequality
--   - generalization: local route changes of the construction that retain incumbent descendant paths → every $s_i$–$t_i$ walk in any game of the §2 model; reason: the proof uses only positivity of the costs, and the construction's substituted walks are instances
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.6 and its proof, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_PoSUndirected_ndGame

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.6 (Physical lifting and cancellation), p.16
(PDF p.18), in the form of the inequality displayed in its proof. Freeze all other strategies and
let `P = Aᵢ` be the mover's old path, with old loads `n_e`; give each edge the unilateral price
`π_P(e) = c_e/n_e` for `e ∈ P` and `c_e/(n_e + 1)` for `e ∉ P`. For every `sᵢ`–`tᵢ` walk `W`
there is a simple `sᵢ`–`tᵢ` path `Q` with `E(Q) ⊆ E(W)` such that, with `R_old = P ∩ E(W)`,
`cᵢ(Q, P₋ᵢ) ≤ Σ_{e ∈ R_old} π_P(e) + Σ_{e ∈ E(W) \ P} π_P(e)`; consequently the gain
`cᵢ(P) − cᵢ(Q, P₋ᵢ)` is at least the abandoned payment `Σ_{e ∈ P \ E(W)} c_e/n_e` minus the
new payment `Σ_{e ∈ E(W) \ P} c_e/(n_e + 1)`.

**Formalization Note.** The printed statement refers forward ("the gain lower bounds used below");
it is formalized as the inequality of its proof and the gain bound derived from it there. -/
theorem lemma_A_6_physical_lifting {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] [Fintype ι] [DecidableEq ι] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (c : E → ℝ) (hc : ∀ e, 0 < c e) (s t : ι → V)
    (A : ι → Finset E) (hA : IsProfile (ndGame ends c s t) A) (i : ι) (W : List E)
    (hW : IsWalk ends (s i) (t i) W) :
    ∃ Q ∈ (ndGame ends c s t).strategies i, Q ⊆ W.toFinset ∧
      cost (ndGame ends c s t) (Function.update A i Q) i ≤
        (∑ e ∈ A i ∩ W.toFinset, c e / (load A e : ℝ)) +
          ∑ e ∈ W.toFinset \ A i, c e / ((load A e : ℝ) + 1) ∧
      (∑ e ∈ A i \ W.toFinset, c e / (load A e : ℝ)) -
          ∑ e ∈ W.toFinset \ A i, c e / ((load A e : ℝ) + 1) ≤
        cost (ndGame ends c s t) A i - cost (ndGame ends c s t) (Function.update A i Q) i := by sorry

end PoSUndirected
