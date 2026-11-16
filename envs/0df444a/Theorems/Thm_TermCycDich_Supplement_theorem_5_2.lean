-- Prove2me | Theorems.Thm_TermCycDich_Supplement_theorem_5_2
-- name    : TermCycDich.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:53:25.731208+00:00
-- url     : https://prove2.me/theorems/1d4680de-984c-42fb-83cc-42762342fa07
-- title:
--   Theorem 5.2 — annulus combing: an $R$-cycle through a large $S$-calm railed annulus can be combed onto at most $2$ rails of a trimming
-- statement:
--   There are functions $f,g,h:\mathbb N^2\to\mathbb N$ with
--
--   $$f(b,n),\;g(b,n),\;h(b,n)\in\mathrm{poly}(b)\cdot\log n+2^{\mathrm{poly}(b)}$$
--
--   such that the following holds for every annotated graph $(G,R)$ with $\mathrm{bidim}(G,R)\le b$, every set $A\subseteq V(G)$, every surface $\Sigma$ and every $\Sigma$-rendition $\rho$ of $G-A$. If $S$ is an $R$-cycle of $G$ and $H=A_{a,s}$ is an $S$-calm railed annulus in $G-A$ and $\rho$ with $a\ge f(b,|G|)$ circles and $s\ge g(b,|G|)$ rails, then there is an $R$-cycle $S^\star$ of $G$ that
--
--   1. is combed in the $h(b,|G|)$-trimming $H^\star$ of $H$, and
--   2. uses at most $2$ rails of $H^\star$.
--
--   The number of rails is a constant independent of $\mathrm{bidim}(G,R)$. The lemma lets the irrelevant-vertex argument of Theorem 1.2 assume that a solution crosses an insulated annulus along at most two rails.
--
--   **Formalization Note** The bounds read: $f,g,h\le p(b)\lfloor\log_2 n\rfloor+2^{q(b)}$ for polynomials $p,q$, and $f\ge2h+2$ so that the trimming is defined. The conclusion asserts that the trimming has a domain inside the domain of $H$ and that $S^\star$ is combed for every such domain.
--
--   Differences from the source:
--   - reading: f5.2, g5.2, h5.2 ∈ poly(b) · log n + 2^poly(b) → f, g, h ≤ p(b)·⌊log₂ n⌋ + 2^{q(b)} for polynomials p, q with natural coefficients (one pair for all three), for all b, n; reason: the base of the logarithm and the split into one pair of polynomials only change the polynomials
--   - reading: the h5.2(b, |G|)-trimming H⋆ of H = A_{a,s} (defined for a = 2h + q, q ≥ 2) → the existential includes f(b, n) ≥ 2h(b, n) + 2, so a ≥ f makes the trimming defined; reason: the trimming must exist for the conclusion to mean anything; the paper's choice f = 22β + 36, h = 11β + 13 satisfies it (p.35)
--   - encoding: H = A_{a,s} a railed annulus → circles and rails given as data (RailData), rails oriented from C₁; the domain O of H is a parameter of 'separating'; reason: the trimming and the rails refer to the decomposition; every railed annulus has such data
--   - reading: S⋆ is combed in H⋆ and uses at most 2 rails of H⋆ → H⋆ has a domain O⋆ ⊆ O (separating), and for every such O⋆ there is a set I of at most 2 rails of H⋆ with S⋆ ∩ K = (⋃_{i∈I} R⋆_i) ∩ K, K the crop by O⋆ minus the vertices of the two boundary circles of H⋆; reason: combing is defined relative to the domain of H⋆, which the paper uses implicitly; all sub-annuli of O bounded by the two traces have the same crop
--   - encoding: surface Σ, Σ-rendition ρ of G − A, traces, C-discs → a type X with IsSurface, the supplement's Rendition of minusVerts G A, traces as relations ('some trace' where a trace is asserted to lie somewhere), the C-disc inside the specified disc; Euler genus < g as Σ(h,c) minus open discs with 2h + c < g; reason: the paper defines traces only up to a slight push; every property used is invariant under the push; Euler genus of a surface with boundary is that of its capped surface
--   - encoding: the trace of every circle is a separating curve in Σ → removing the trace disconnects the connected component of Σ containing it; reason: equal to 'Σ − T is disconnected' on a connected surface; Theorem 5.2 allows every surface
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 5.2, p.35 (PDF 37); railed annuli, S-calm, trimming and combed R-cycles p.34 (PDF 36); f5.2, h5.2 p.35 (PDF 37)

import Mathlib
import Definitions.Def_TermCycDich_IsRCycle
import Definitions.Def_TermCycDich_bidim
import Definitions.Def_TermCycDich_Supplement_RailedAnnulus

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-- **Theorem 5.2** (annulus combing lemma for `R`-cycles).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), Theorem 5.2, p.35 (PDF 37): "There exist functions f5.2, g5.2,
h5.2 : N² → N such that for every instance (G, R) of Terminal Cyclability with bidim(G, R) ≤ b,
every set A ⊆ V(G), every surface Σ, and every Σ-rendition ρ of G − A, the following holds: If S is
an R-cycle in G and H = A_{a,s} is an S-calm railed annulus with a ≥ f5.2(b, |G|) and
s ≥ g5.2(b, |G|) in G − A and ρ, then there exists an R-cycle S⋆ in G such that i) S⋆ is combed in
the h5.2(b, |G|)-trimming H⋆ of H, and ii) S⋆ uses at most 2 rails of H⋆. Moreover, f5.2(b, n),
g5.2(b, n), h5.2(b, n) ∈ poly(b) · log n + 2^poly(b)."

**Formalization Note**
* `∈ poly(b) · log n + 2^poly(b)`: each of `f, g, h` is at most `p(b) · ⌊log₂ n⌋ + 2^{q(b)}` for
  polynomials `p, q` with natural coefficients (one pair for all three).
* The `h`-trimming of `A_{a,s}` needs `a = 2h + q` with `q ≥ 2`; the existential includes
  `f ≥ 2h + 2`, so `a ≥ f` makes the trimming defined (the paper's choice satisfies it).
* `H` is given with its circles and rails (`RailData`), a railed annulus inside `G − A`,
  separating in `ρ` with domain `O`, and `S`-calm (blank and avoiding `N_S(A ∩ V(S))`).
* The conclusion is about the trimming `H⋆` (circles `C_{h+1}, …, C_{a-h}`, rails cut to their
  minimal subpaths) and its domain, the sub-annulus `O⋆ ⊆ O` with boundary the traces of its two
  boundary circles: such a domain exists, and for every such `O⋆` (they all have the same crop) the
  cycle `S⋆` is combed in `H⋆` using at most two rails.
* `Σ` is any surface (no genus bound, possibly disconnected), and `ρ` any `Σ`-rendition of `G − A`
  (not necessarily blank). -/
theorem theorem_5_2 :
    ∃ (f g h : ℕ → ℕ → ℕ) (p q : Polynomial ℕ),
      (∀ b n, f b n ≤ p.eval b * Nat.log 2 n + 2 ^ q.eval b ∧
        g b n ≤ p.eval b * Nat.log 2 n + 2 ^ q.eval b ∧
        h b n ≤ p.eval b * Nat.log 2 n + 2 ^ q.eval b) ∧
      (∀ b n, 2 * h b n + 2 ≤ f b n) ∧
      ∀ (b : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V),
        bidim G R ≤ b → ∀ (A : Finset V) (X : Type) [TopologicalSpace X], IsSurface X →
        ∀ (ρ : Rendition X (minusVerts G (A : Set V))) {u : V} (S : G.Walk u u),
          IsRCycle G R S →
          ∀ (a s : ℕ) (H : RailData G a s) (O : Set X),
            IsRailedAnnulus (minusVerts G (A : Set V)) H → ρ.IsSeparatingWith H O →
            ρ.IsCalm R (A : Set V) S O →
            f b (Fintype.card V) ≤ a → g b (Fintype.card V) ≤ s →
            ∃ (u' : V) (S' : G.Walk u' u'), IsRCycle G R S' ∧
              ∀ H' : RailData G (a - 2 * h b (Fintype.card V)) s,
                IsTrimming H (h b (Fintype.card V)) H' →
                (∃ O' ⊆ O, ρ.IsSeparatingWith H' O') ∧
                ∀ O' ⊆ O, ρ.IsSeparatingWith H' O' →
                  ∃ I : Finset (Fin s), I.card ≤ 2 ∧ ρ.CombedUsing O' H' S' I := by sorry

end Supplement

end TermCycDich
