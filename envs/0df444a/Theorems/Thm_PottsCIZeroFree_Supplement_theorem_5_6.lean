-- Prove2me | Theorems.Thm_PottsCIZeroFree_Supplement_theorem_5_6
-- name    : PottsCIZeroFree.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:36:53.219632+00:00
-- url     : https://prove2.me/theorems/57a330f7-61a5-4808-937c-def25a8bfc49
-- title:
--   Theorem 5.6 (Log-concave Holant polytube) — graph-uniform zero-free polytubes around $[0,R]^E$
-- statement:
--   Fix an integer $\Delta\ge2$ and a finite family $\mathcal F$ of log-concave symmetric Boolean signatures with $f(0)>0$ for every $f\in\mathcal F$. For every $R>0$ there is $\varepsilon=\varepsilon(\Delta,\mathcal F,R)>0$ such that the following holds. For every finite simple graph $G=(V,E)$ of maximum degree at most $\Delta$, every assignment $(f_v)_{v\in V}$ with $f_v\in\mathcal F$ of arity $\deg_G(v)$, and every $\mathbf z\in\mathbb C^E$,
--   $$Z_{G,\mathbf f}(\mathbf z)\neq0\qquad\text{whenever }\mathbf z\in\mathcal U_\varepsilon([0,R])^E,$$
--   where $\mathcal U_\varepsilon([0,R])=\{z\in\mathbb C:\operatorname{dist}(z,[0,R])<\varepsilon\}$ and each activity is perturbed independently. In particular:
--   1. the union $\bigcup_{R>0}\mathcal U_{\varepsilon(\Delta,\mathcal F,R)}([0,R])^E$ is an open zero-free neighborhood of $[0,\infty)^E$;
--   2. on the diagonal $z_e=z$, $Z_{G,\mathbf f}(z\mathbf 1)\neq0$ throughout the open set
--   $$U_{\Delta,\mathcal F}=\bigcup_{R>0}\mathcal U_{\varepsilon(\Delta,\mathcal F,R)}([0,R])\supset[0,\infty),$$
--   which depends only on $(\Delta,\mathcal F)$ and is common to all the graphs and signature assignments above.
--
--   This gives zero-free regions for log-concave Boolean Holant problems that are uniform over bounded-degree graphs and contain every bounded box of nonnegative activities.
--
--   **Formalization Note** $\varepsilon$ is a function of $R$, chosen after $(\Delta,\mathcal F)$ and before the graph; the "in particular" clauses are stated with that same function. Activities are `z : G.edgeSet → ℂ`; $\deg_G(v)$ is the number of neighbors of $v$; $\mathcal U_\varepsilon(I)$ is the published `nbhd`.
--
--   Differences from the source:
--   - encoding: $\varepsilon=\varepsilon(\Delta,\mathcal F,R)$ for every $R>0$ → one function `ε : ℝ → ℝ` with `ε R > 0` for `R > 0`, chosen before the graph; reason: equivalent by choice, and it lets the union over $R$ be written.
--   - encoding: signature $f:\{0,\dots,d\}\to[0,\infty)$ → structure `SymSig` with `arity`, `val : Fin (arity+1) → ℝ`, `0 ≤ val`, evaluated as $0$ past the arity; reason: same signatures, and values past the arity never occur.
--   - encoding: "open zero-free neighborhood of $[0,\infty)^E$" → three clauses: the union is open, contains $[0,\infty)^E$, and zero-freeness on each polytube (the main clause); reason: same content.
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), Theorem 5.6, p.30 (PDF p.32); signatures, log-concavity, (44), p.29 (PDF p.31); $\mathcal U_\varepsilon$ p.2 (PDF p.4)

import Mathlib
import Definitions.Def_PottsCIZeroFree_normPinnedPoly
import Definitions.Def_PottsCIZeroFree_Supplement_holantPoly

open Classical

namespace PottsCIZeroFree.Supplement

open PottsCIZeroFree

/-- Theorem 5.6 (Log-concave Holant polytube) of Shao, Shi, *Coupling Independence Implies
Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.30 (PDF p.32). Fix an integer
`Δ ≥ 2` and a finite family `ℱ` of log-concave symmetric Boolean signatures with `f(0) > 0` for
every `f ∈ ℱ`. For every `R > 0` there is `ε = ε(Δ, ℱ, R) > 0` such that, for every finite
simple graph `G = (V, E)` of maximum degree at most `Δ`, every assignment `(f_v)` with
`f_v ∈ ℱ` of arity `deg_G(v)`, and every `z ∈ ℂ^E`, `Z_{G,f}(z) ≠ 0` whenever
`z ∈ U_ε([0, R])^E`. In particular the union `⋃_{R>0} U_{ε(R)}([0, R])^E` is an open zero-free
neighborhood of `[0, ∞)^E`, and on the diagonal `Z_{G,f}(z𝟏) ≠ 0` throughout the open set
`U_{Δ,ℱ} = ⋃_{R>0} U_{ε(R)}([0, R]) ⊃ [0, ∞)`, common to all graphs and assignments.

**Formalization Note.** `ε` is a function of `R` chosen after `Δ, ℱ` and before the graph,
which is how "`ε = ε(Δ, ℱ, R)`" and the union over `R` are expressed. `U_ε([0,R])^E` is the set
of `z : G.edgeSet → ℂ` with every coordinate in `nbhd ε (Icc 0 R)`, each coordinate perturbed
independently. `deg_G(v)` is `(G.neighborSet v).ncard`. -/
theorem theorem_5_6 (Δ : ℕ) (hΔ : 2 ≤ Δ) (ℱ : Finset SymSig) (hLC : ∀ f ∈ ℱ, f.LogConcave)
    (h0 : ∀ f ∈ ℱ, 0 < f.eval 0) :
    ∃ ε : ℝ → ℝ, (∀ R : ℝ, 0 < R → 0 < ε R) ∧
      (∀ {V : Type} [Fintype V] (G : SimpleGraph V), MaxDegLE G Δ →
        ∀ f : V → SymSig, (∀ v, f v ∈ ℱ ∧ (f v).arity = (G.neighborSet v).ncard) →
          (∀ R : ℝ, 0 < R → ∀ z : G.edgeSet → ℂ,
              (∀ e, z e ∈ nbhd (ε R) (Set.Icc 0 R)) → holantPoly G f z ≠ 0) ∧
          IsOpen (⋃ R ∈ Set.Ioi (0 : ℝ),
              {z : G.edgeSet → ℂ | ∀ e, z e ∈ nbhd (ε R) (Set.Icc 0 R)}) ∧
          (∀ x : G.edgeSet → ℝ, (∀ e, 0 ≤ x e) →
              (fun e => (x e : ℂ)) ∈ ⋃ R ∈ Set.Ioi (0 : ℝ),
                {z : G.edgeSet → ℂ | ∀ e, z e ∈ nbhd (ε R) (Set.Icc 0 R)}) ∧
          (∀ w ∈ ⋃ R ∈ Set.Ioi (0 : ℝ), nbhd (ε R) (Set.Icc 0 R),
              holantPoly G f (fun _ => w) ≠ 0)) ∧
      IsOpen (⋃ R ∈ Set.Ioi (0 : ℝ), nbhd (ε R) (Set.Icc 0 R)) ∧
      (∀ x : ℝ, 0 ≤ x → (x : ℂ) ∈ ⋃ R ∈ Set.Ioi (0 : ℝ), nbhd (ε R) (Set.Icc 0 R)) := by sorry

end PottsCIZeroFree.Supplement
