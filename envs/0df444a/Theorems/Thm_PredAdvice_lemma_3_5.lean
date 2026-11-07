-- Prove2me | Theorems.Thm_PredAdvice_lemma_3_5
-- name    : PredAdvice.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:38.141914+00:00
-- url     : https://prove2.me/theorems/7a76a547-03c5-423f-a792-c5a7a324b438
-- title:
--   Lemma 3.5 — $|\hat H_F| \le \sum_u |F^{out}_u| + \sum_v |F^{in}_v| = O(LD^2n^2/RS(n))$
-- statement:
--   There is an absolute constant $C$ such that, for every directed unweighted graph $G=(V,E)$ with $|V|=n$, every $2\le D\le n$, $L\ge1$, all colourings $\chi$ and all maximal matchings $M^{h,j}_{d,c}$:
--
--   1. $|\hat H_F|\le\sum_{u}|F^{out}_u|+\sum_{v}|F^{in}_v|$;
--   2. $\sum_{u}|F^{out}_u|+\sum_{v}|F^{in}_v|\le C\,LD^2n^2/RS(n)$ (eq. (8));
--   3. for every $j\in[L]$, $1\le d<D$, $c\in[3D]$, the graph $G^j_{d,c}=\bigcup_{h}M^{h,j}_{d,c}$ on $(V_L,V_R)$ is an edge-disjoint union of the matchings $M^{h,j}_{d,c}$, each induced in $G^j_{d,c}$, and $|E(G^j_{d,c})|\le C\,n^2/RS(n)$.
--
--   This is where the Ruzsa–Szemerédi function enters the bounds of the paper.
--
--   Differences from the source:
--   - generalization: the colourings and matchings fixed in §3.2–3.3 → any colourings and any family of maximal matchings; reason: the proof uses no property of the specific choice
--   - generalization: the inequality and O(·) of (8) → also the claim of the proof (edge-disjoint union of induced matchings with O(n²/RS(n)) edges); reason: a stated step of the proof; dropping it gives the printed lemma
--   - encoding: O(·) → one absolute constant C chosen before V, G, D, L, χ, M; reason: standard reading of O(·)
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 3.5, eq. (8), p.13, and the claim of its proof, pp.13–14

import Mathlib
import Definitions.Def_PredAdvice_HF
import Definitions.Def_PredAdvice_RS

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 3.5** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.3, eq. (8), p.13, with the claim of its proof, pp.13–14). Let
`2 ≤ D ≤ n = |V|`, `L ≥ 1`, and let `χ` and the maximal matchings `M^{h,j}_{d,c}` be arbitrary.
Then

1. `|Ĥ_F| ≤ ∑_u |F^out_u| + ∑_v |F^in_v|`, and
2. `∑_u |F^out_u| + ∑_v |F^in_v| = O(L D² n² / RS(n))`;
3. (the claim of the proof) for every `j ∈ [L]`, `1 ≤ d < D`, `c ∈ [3D]`, the graph
   `G^j_{d,c} := ⋃_h M^{h,j}_{d,c}` on `(V_L, V_R)` is an edge-disjoint union of the matchings
   `M^{h,j}_{d,c}`, each induced in `G^j_{d,c}`, and `|E(G^j_{d,c})| = O(n²/RS(n))`.

**Formalization Note** One absolute constant `C` serves both `O(·)`; it is chosen before `V`, `G`,
`D`, `L`, `χ` and `M`. Inducedness of `M^{h,j}_{d,c}` in `G^j_{d,c}`: for two distinct edges
`(a, b), (a′, b′)` of it, neither `(a, b′)` nor `(a′, b)` is an edge of any `M^{h′,j}_{d,c}`. -/
theorem lemma_3_5 :
    ∃ C : ℝ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ)
      (χ : Colorings V D L) (M : ℕ → ℕ → Fin L → V → Finset (V × V)),
      2 ≤ D → D ≤ Fintype.card V → 1 ≤ L → IsMatchingFamily G χ M →
        (HF D M).card ≤ ∑ u, (FOut D M u).card + ∑ v, (FIn D M v).card ∧
        ((∑ u, (FOut D M u).card + ∑ v, (FIn D M v).card : ℕ) : ℝ) ≤
          C * ((L : ℝ) * (D : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 2 / RS (Fintype.card V)) ∧
        ∀ d c : ℕ, ∀ j : Fin L, 1 ≤ d → d < D → 1 ≤ c → c ≤ 3 * D →
          (∀ h h' : V, h ≠ h' → Disjoint (M d c j h) (M d c j h')) ∧
          (∀ h : V, ∀ p ∈ M d c j h, ∀ q ∈ M d c j h, p ≠ q → ∀ h' : V,
              (p.1, q.2) ∉ M d c j h' ∧ (q.1, p.2) ∉ M d c j h') ∧
          ((∑ h, (M d c j h).card : ℕ) : ℝ) ≤
            C * ((Fintype.card V : ℝ) ^ 2 / RS (Fintype.card V)) := by sorry

end PredAdvice
