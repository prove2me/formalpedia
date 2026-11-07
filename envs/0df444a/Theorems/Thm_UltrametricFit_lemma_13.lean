-- Prove2me | Theorems.Thm_UltrametricFit_lemma_13
-- name    : UltrametricFit.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:41.252361+00:00
-- url     : https://prove2.me/theorems/6e1b3c8d-6bc5-4053-98b7-d68b933c9479
-- title:
--   Lemma 13, p.11 — the cost of one merge biclique against its LP cost
-- statement:
--   Let $\Gamma_0=1+\frac{1-\delta}{\delta(1-2\delta)^2}$ and $\Gamma=\frac{2}{((\Gamma_0+1)/\Gamma_0)^{1/p}-1}$. For $\delta\in(0,1/2)$, $p\ge1$, a feasible $x$ and each node $(A\cup B,\ell^*)$ of the final forest of a run on $x$,
--   $$\bigl(\mathrm{cost}(A,B,\ell^*)\bigr)^{1/p}\le\Gamma\,\bigl(\mathrm{lp}(A\times B,x)\bigr)^{1/p}.$$
--   This is the per-biclique form of the guarantee of the algorithm.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of the LP (§3) → $x$ any feasible point; reason: optimal solutions are feasible, so the page's case is included
--   - encoding: Algorithm 1 with unspecified merge order → a relation `IsRun` with a universal quantifier over runs, and a relational output `IsOutput`; reason: the paper fixes no order (and §5 speaks of the worst one), so every order is an execution of the algorithm
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
--   - encoding: a node $(A\cup B,\ell^*)$ of the final forest $T_L$ → a merge event $(\ell^*,A,B)$ in the list `mergeEvents` of a run; reason: the nodes of $T_L$ other than leaves are exactly the merges of the run; the forest is not a separate object
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Lemma 13, p.11

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun
import Definitions.Def_UltrametricFit_errLayer

namespace UltrametricFit

/-- **Lemma 13**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.11: for each
node `(A ∪ B, ℓ*)` of `T_L`, `cost(A, B, ℓ*)^{1/p} ≤ Γ · lp(A × B, x)^{1/p}`.

**Formalization Note.** The node is a merge event of a run on a feasible `x`; §3's "optimal" is not
used. -/
theorem lemma_13 {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (x : ℕ → Fin n → Fin n → ℝ) (hx : IsFeasible X x) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (p : ℝ) (hp : 1 ≤ p) (C : ℕ → Finset (Finset (Fin n)))
    (M : ℕ → List (Finset (Fin n) × Finset (Fin n))) (hrun : IsRun X x δ C M)
    (e : ℕ × Finset (Fin n) × Finset (Fin n)) (he : e ∈ mergeEvents X M) :
    mergeCost X p e.1 e.2.1 e.2.2 ^ (1 / p) ≤
      Gamma δ p * lpBiclique X p x e.2.1 e.2.2 ^ (1 / p) := by sorry

end UltrametricFit
