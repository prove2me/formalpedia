-- Prove2me | Theorems.Thm_UltrametricFit_lemma_13_second_term
-- name    : UltrametricFit.lemma_13_second_term
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:29.29533+00:00
-- url     : https://prove2.me/theorems/b2e0be71-1455-4d81-9a32-db2325ff9245
-- title:
--   Appendix A, pp.31–32 — the second term of (12)
-- statement:
--   Let $x$ be feasible, $\delta\in(0,1/2)$, $p\ge1$, and $(\ell^*,A,B)$ a merge event of a run on $x$. Writing $(y)_+=\max\{0,y\}$,
--   $$\Bigl(\sum_{i\in A,\,j\in B}(X(i,j)-D_{\ell^*})_+^p\Bigr)^{1/p}\le\frac{\Gamma}{2}\,\bigl(\mathrm{lp}(A\times B,x)\bigr)^{1/p}.$$
--   This term measures the pairs whose input distance is above the layer at which the algorithm merged them.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of the LP (§3) → $x$ any feasible point; reason: optimal solutions are feasible, so the page's case is included
--   - encoding: Algorithm 1 with unspecified merge order → a relation `IsRun` with a universal quantifier over runs, and a relational output `IsOutput`; reason: the paper fixes no order (and §5 speaks of the worst one), so every order is an execution of the algorithm
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
--   - encoding: a node $(A\cup B,\ell^*)$ of the final forest $T_L$ → a merge event $(\ell^*,A,B)$ in the list `mergeEvents` of a run; reason: the nodes of $T_L$ other than leaves are exactly the merges of the run; the forest is not a separate object
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Appendix A, pp.31–32, second term of (12)

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsRun
import Definitions.Def_UltrametricFit_errLayer

namespace UltrametricFit

/-- **Proof of Lemma 13, second term of (12)**, Charikar, Gao, STOC 2027 submission (manuscript
sha256 87af12a2…), Appendix A, pp.31–32: for a merge event `(ℓ*, A, B)` of a run on a feasible `x`,
`(Σ_{i∈A, j∈B} (X(i, j) − D_{ℓ*})₊^p)^{1/p} ≤ (Γ/2) · lp(A × B, x)^{1/p}`.

**Formalization Note.** `(y)₊ = max{0, y}` is written `max y 0`. -/
theorem lemma_13_second_term {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (x : ℕ → Fin n → Fin n → ℝ) (hx : IsFeasible X x) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (p : ℝ) (hp : 1 ≤ p) (C : ℕ → Finset (Finset (Fin n)))
    (M : ℕ → List (Finset (Fin n) × Finset (Fin n))) (hrun : IsRun X x δ C M)
    (e : ℕ × Finset (Fin n) × Finset (Fin n)) (he : e ∈ mergeEvents X M) :
    (∑ i ∈ e.2.1, ∑ j ∈ e.2.2, (max (X i j - layerValue X e.1) 0) ^ p) ^ (1 / p) ≤
      Gamma δ p / 2 * lpBiclique X p x e.2.1 e.2.2 ^ (1 / p) := by sorry

end UltrametricFit
