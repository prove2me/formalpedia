-- Prove2me | Theorems.Thm_PermInvCC_lemma_4_5
-- name    : PermInvCC.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:34.994841+00:00
-- url     : https://prove2.me/theorems/16257e3c-1728-4cb6-8899-8f08ed7ee5b7
-- title:
--   Lemma 4.5 — counts along a maximum-weight spanning tree
-- statement:
--   Let $q\ge2$ and let $T\ne U$ be types with the same margins, with $h:=h(T,U)<1/(64q^2)$. Let $v=v^+-v^-$ be the signed matrix of a simple alternating cycle, $g\ge1$ an integer, and
--   $$S^-=C+gv^-,\qquad S^+=C+gv^+,$$
--   where $C$ is a nonnegative integer table and both $S^-$ and $S^+$ lie entrywise between $T$ and $U$. Give each edge $e$ of the bipartite symbol graph weight $C_e$, and let $\tau$ be a spanning tree of maximum total weight. For each cycle edge $e\notin\tau$ let $P_e$ be the tree path joining its endpoints and $\lambda_e:=\min_{e'\in P_e}C_{e'}$. Then, for every such edge $e$,
--   $$C_e\le\lambda_e,\qquad (C_e+g)\lambda_e\ge\frac{g^2}{16q^2h^2},\qquad\lambda_e\ge8qg.$$
--
--   A purely combinatorial lemma: it supplies the long intervals of types that Lemma 4.4 needs.
--
--   Differences from the source:
--   - encoding: a spanning tree of K_{q,q} of maximum total weight → a cell set τ whose graph on all 2q symbols is a tree, maximizing ∑_{e∈τ} C_e over all such sets; reason: Lean representation of spanning trees of the complete bipartite graph
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 4.5, eq. (4.7), p.18

import Mathlib
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_hE
import Definitions.Def_PermInvCC_AltCycle
import Definitions.Def_PermInvCC_symbolGraph
import Definitions.Def_PermInvCC_treePath

namespace PermInvCC

/-- **Lemma 4.5 (Counts Along a Maximum-Weight Spanning Tree)** (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, p.18). Let `T ≠ U` be types with the same
margins, `h := h(T, U) < 1/(64q²)`. Let `v = v⁺ − v⁻` be the signed matrix of a simple
alternating cycle, `g ≥ 1` an integer, and `S⁻ = C + gv⁻`, `S⁺ = C + gv⁺`, where `C` is a
nonnegative integer table and both `S⁻, S⁺` lie entrywise between `T` and `U`. Give each edge `e`
of the bipartite symbol graph weight `C_e`, and let `τ` be a spanning tree of maximum total
weight. For each cycle edge `e ∉ τ` let `P_e` be the tree path joining its endpoints and
`λ_e := min_{e'∈P_e} C_{e'}` (4.7). Then `C_e ≤ λ_e`, `(C_e + g)λ_e ≥ g²/(16q²h²)` and
`λ_e ≥ 8qg`.

**Formalization Note.** Types are tables; equal margins force equal totals. A spanning tree is a set `τ` of cells
whose graph on all `2q` symbols is a tree; maximality is over all such sets. "Entrywise between"
is `min(T_e, U_e) ≤ S_e ≤ max(T_e, U_e)`. `q ≥ 2` is the standing assumption (p.9). -/
theorem lemma_4_5 (q : ℕ) (hq : 2 ≤ q) (T U : Fin q → Fin q → ℕ)
    (hne : T ≠ U)
    (hrow : ∀ a, rowMargin T a = rowMargin U a) (hcol : ∀ b, colMargin T b = colMargin U b)
    (hsmall : hTU T U < 1 / (64 * (q : ℝ) ^ 2))
    (v : AltCycle q) (g : ℕ) (hg : 1 ≤ g) (C : Fin q → Fin q → ℕ)
    (hminus : ∀ a b, min (T a b) (U a b) ≤ C a b + g * v.vminus a b ∧
      C a b + g * v.vminus a b ≤ max (T a b) (U a b))
    (hplus : ∀ a b, min (T a b) (U a b) ≤ C a b + g * v.vplus a b ∧
      C a b + g * v.vplus a b ≤ max (T a b) (U a b))
    (τ : Finset (Fin q × Fin q)) (hτ : (symbolGraph τ).IsTree)
    (hmax : ∀ τ' : Finset (Fin q × Fin q), (symbolGraph τ').IsTree →
      ∑ e ∈ τ', C e.1 e.2 ≤ ∑ e ∈ τ, C e.1 e.2) :
    ∀ e ∈ v.edges, e ∉ τ →
      C e.1 e.2 ≤ lamE τ C e ∧
      (g : ℝ) ^ 2 / (16 * (q : ℝ) ^ 2 * hTU T U ^ 2) ≤
        ((C e.1 e.2 : ℝ) + g) * (lamE τ C e : ℝ) ∧
      8 * q * g ≤ lamE τ C e := by sorry

end PermInvCC
