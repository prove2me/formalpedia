-- Prove2me | Theorems.Thm_TermCycDich_Supplement_theorem_3_8
-- name    : TermCycDich.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:51:01.797295+00:00
-- url     : https://prove2.me/theorems/e910f3fa-5bf4-4291-9b8a-a38892b2b4fd
-- title:
--   Theorem 3.8 — a vital instance of bidimensionality $b$ and treewidth $\ge f_{3.8}(b,w)\in\mathrm{poly}(b)\cdot w$ has a $(w,b)$-village
-- statement:
--   There is a function $f_{3.8}:\mathbb N^2\to\mathbb N$ with $f_{3.8}(b,w)\in\mathrm{poly}(b)\cdot w$ such that for all integers $b\ge1$ and $w\ge3$: if $(G,R)$ is a vital instance of Terminal Cyclability (it has a unique $R$-cycle $S$, and $S$ spans $G$) with
--
--   $$\mathrm{tw}(G)\ge f_{3.8}(b,w)\qquad\text{and}\qquad \mathrm{bidim}(G,R)=b,$$
--
--   then $(G,R)$ has a $(w,b)$-village $(G,R,S,A,\rho,\Sigma,\Delta,\mathcal C)$: an apex set $A$, a surface $\Sigma$ of bounded Euler genus, a blank rendition $\rho$ of $(G-A,R\setminus A)$ of bounded breadth and depth, and a vortex-free disc $\Delta$ carrying $w$ concentric cycles whose crop avoids the $S$-neighbours of $A$.
--
--   This is the first structural refinement in the proof of Theorem 1.3: large treewidth of a vital instance forces a large insulated planar region.
--
--   **Formalization Note** The village refers to the functions $\mathrm{apex}_{2.4}$, $\mathrm{depth}_{2.4}$ of the cited Proposition 2.4, which are known only to exist and to be polynomial in $k+t+r$; the statement asserts the existence of such polynomially bounded functions together with $f_{3.8}$.
--
--   Differences from the source:
--   - reading: the functions apex2.4, depth2.4 of the cited Proposition 2.4 [GPW26], with apex2.4(k,t,r), depth2.4(k,t,r) ∈ poly(k + t + r) → ∃ apex depth : ℕ → ℕ → ℕ → ℕ and a polynomial p with natural coefficients, apex(k,t,r), depth(k,t,r) ≤ p(k + t + r); reason: the paper fixes these functions only through Proposition 2.4's existence statement and this bound
--   - reading: f(b, w) ∈ poly(b) · w → f(b, w) ≤ q(b) · w for a polynomial q with natural coefficients, for all b ≥ 1, w ≥ 3; reason: the poly convention of the published Theorem 1.3
--   - encoding: tw(G) ≥ f(b, w) → every k with TreewidthLE G k satisfies f(b, w) ≤ k; reason: equivalent to tw(G) ≥ f(b, w)
--   - encoding: surface Σ, Σ-rendition ρ of G − A, traces, C-discs → a type X with IsSurface, the supplement's Rendition of minusVerts G A, traces as relations ('some trace' where a trace is asserted to lie somewhere), the C-disc inside the specified disc; Euler genus < g as Σ(h,c) minus open discs with 2h + c < g; reason: the paper defines traces only up to a slight push; every property used is invariant under the push; Euler genus of a surface with boundary is that of its capped surface
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 3.8, p.26 (PDF 28); village definition p.26 (PDF 28)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_TermCycDich_Supplement_Village

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-- **Theorem 3.8** (large treewidth yields a village).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), Theorem 3.8, p.26 (PDF 28): "There exists a function
f3.8 : N² → N such that for all integers b ≥ 1 and w ≥ 3, if (G, R) is a vital instance of
Terminal Cyclability with tw(G) ≥ f3.8(b, w) and bidim(G, R) = b, then there exists a
(w, b)-village for (G, R). Moreover, f3.8(b, w) ∈ poly(b) · w."

**Formalization Note**
* The village (`IsVillage`) refers to the functions `apex2.4`, `depth2.4` of the cited
  Proposition 2.4 [GPW26], which the paper fixes only by their existence and the bound
  `apex2.4(k,t,r), depth2.4(k,t,r) ∈ poly(k + t + r)`; they are therefore quantified as some
  functions bounded by a polynomial `p` in `k + t + r`.
* `f3.8(b, w) ∈ poly(b) · w`: `f(b, w) ≤ q(b) · w` for a polynomial `q` with natural coefficients,
  for all `b ≥ 1`, `w ≥ 3`.
* `tw(G) ≥ f`: every tree-decomposition width `k` achieved by `G` (public `TreewidthLE G k`)
  satisfies `f ≤ k`.
* The surface `Σ` is a type `X` with a topology; the rendition is of `G − A` (public
  `minusVerts`). -/
theorem theorem_3_8 :
    ∃ (apex depth : ℕ → ℕ → ℕ → ℕ) (p : Polynomial ℕ),
      (∀ k t r, apex k t r ≤ p.eval (k + t + r) ∧ depth k t r ≤ p.eval (k + t + r)) ∧
      ∃ (f : ℕ → ℕ → ℕ) (q : Polynomial ℕ),
        (∀ b w, 1 ≤ b → 3 ≤ w → f b w ≤ q.eval b * w) ∧
        ∀ b w : ℕ, 1 ≤ b → 3 ≤ w →
          ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V),
            IsVital G R → (∀ k, RobertsonSeymour1986.GM5.TreewidthLE G k → f b w ≤ k) →
            bidim G R = b →
            ∃ (u : V) (S : G.Walk u u) (A : Finset V) (X : Type) (_ : TopologicalSpace X)
              (ρ : Rendition X (minusVerts G (A : Set V))) (Δ : Set X)
              (C : Fin w → G.Subgraph),
              IsVillage apex depth w b G R S A X ρ Δ C := by sorry

end Supplement

end TermCycDich
