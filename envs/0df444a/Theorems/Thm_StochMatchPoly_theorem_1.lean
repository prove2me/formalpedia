-- Prove2me | Theorems.Thm_StochMatchPoly_theorem_1
-- name    : StochMatchPoly.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:26:06.175607+00:00
-- url     : https://prove2.me/theorems/2ef0ea7e-86a2-4be1-a5aa-c06d5ac6708e
-- title:
--   Theorem 1 — Sample-and-Union gives $\Delta(H)\le R$ and $(1-\varepsilon)\,\mathbb E\,\mu(G_p)$ (corrected: degree bound $C(1+\log(1/\varepsilon))/(p\varepsilon^4)$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G=(V,E)$ be a finite simple graph, $p\in(0,1]$, $\varepsilon\in(0,1)$, and let $G_p$ be the random subgraph keeping each edge independently with probability $p$. Let $\mathrm{MM}$ be any rule choosing a maximum matching of each subgraph of $G$, and let $R$ be any integer with
--
--   $$R\ge\frac{C\,(1+\log(1/\varepsilon))}{p\,\varepsilon^4}.$$
--
--   Run Algorithm 1 (Sample-and-Union): draw $R$ independent samples $G^{(1)},\dots,G^{(R)}\sim G_p$ and output $H$ with $E(H)=\mathrm{MM}(G^{(1)})\cup\dots\cup\mathrm{MM}(G^{(R)})$. Then
--
--   1. every output $H$ is a subgraph of $G$ with maximum degree $\Delta(H)\le R$;
--   2. with $G_p$ independent of the samples,
--   $$\mathbb E_{H,G_p}\,\mu(H\cap G_p)\ge(1-\varepsilon)\,\mathbb E\,\mu(G_p);$$
--   3. there is a fixed subgraph $H\subseteq G$ with $\Delta(H)\le R$ and $\mathbb E\,\mu(H\cap G_p)\ge(1-\varepsilon)\,\mathbb E\,\mu(G_p)$.
--
--   For $\varepsilon\le 1/2$ the degree bound is $O(\log(1/\varepsilon)/(p\varepsilon^4))$, polynomial in $1/(\varepsilon p)$, which settles the conjecture of Behnezhad, Derakhshan and Hajiaghayi (STOC 2020).
--
--   **Formalization Note** Expectations are finite sums over edge subsets (`expect`, `sampleExpect`); $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - correction: maximum degree R = O(log(1/ε)/(pε⁴)) for every ε ∈ (0, 1), with absolute constants (§4.1) → R ≥ C(1 + log(1/ε))/(pε⁴); reason: as printed the bound is false near ε = 1: for G a single edge and p = 1, E µ(Gp) = 1 and R = 0 gives E µ(H ∩ Gp) = 0 < 1 − ε, so R ≥ 1 is needed, while C·log(1/ε)/(pε⁴) → 0 as ε → 1; the proof's own R = ⌈log(1/δ)/(pδ⁴)⌉ with δ = cε (15) is of the corrected form, and the corrected bound is the printed order for ε ≤ 1/2
--   - generalization: the output of Algorithm 1 with R = O(·) samples → every R : ℕ with C(1 + log(1/ε))/(pε⁴) ≤ R; reason: the proof only uses e^{−Rτ} ≤ δ and 1/R ≤ τ, both monotone in R; it specializes to R = ⌈C(1 + log(1/ε))/(pε⁴)⌉
--   - encoding: MM, 'the matching chosen by the fixed rule', a maximum matching → ∀ MM with IsMaxMatchingRule G.edgeFinset MM, quantified after C; reason: the statement holds for the paper's fixed rule, whichever it is; q_e is defined with the same MM
--   - encoding: 'achieves a (1 − ε)-approximation with maximum degree R' (with (1) and the closing paragraph, p.17) → three conjuncts: ∆(H) ≤ R and H ⊆ G for every output; E_{H,Gp} µ(H ∩ Gp) ≥ (1 − ε) E µ(Gp) over R + 1 independent copies of Gp; a fixed H ⊆ G with ∆(H) ≤ R and the same guarantee; reason: p.17: 'every output satisfies ∆(H) ≤ R' and 'there exists a fixed subgraph H with the same expected approximation guarantee'; the fixed-H form is Result 1
--   - encoding: expectations over Gp and the samples → finite weighted sums over subsets of G's edges with the product weight ∏ p^{[e∈S]}(1 − p)^{[e∉S]}; reason: Lean convention; the law sums to 1 (sanity file)
--   - encoding: every graph G → a finite simple graph (SimpleGraph on a Fintype V); reason: §4.1: all graphs in the main argument are finite, undirected and simple
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Theorem 1, p.9 (PDF p.10); goal (1), p.1 (PDF p.2); Algorithm 1, p.9; closing paragraph of the proof, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_StochMatchPoly_edgeLaw
import Definitions.Def_StochMatchPoly_sampleUnion

open Classical

universe u

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Theorem 1, p.9 (PDF p.10), with goal (1) of p.1, Algorithm 1 of p.9 and the
closing paragraph of the proof, p.17. **Corrected:** degree bound `C (1 + log(1/ε))/(p ε⁴)`.

"Theorem 1. For every graph G, p ∈ (0, 1], and ε ∈ (0, 1), the output H of Algorithm 1 achieves a
(1 − ε)-approximation with maximum degree R = O(log(1/ε)/(pε⁴))." Goal (1): "E µ(H ∩ Gp) ≥
(1 − ε) E µ(Gp)". p.17: "Since H is the union of R matchings, every output satisfies ∆(H) ≤ R.
Moreover, averaging over the randomness of H shows that there exists a fixed subgraph H with the
same expected approximation guarantee."

**Formalization Note.**
1. Graphs are finite simple graphs (§4.1); constants are absolute (§4.1), so `C` comes first.
2. Correction: as printed, `R = O(log(1/ε)/(pε⁴))` fails as `ε → 1` (one edge, `p = 1`: `R = 0`
   gives `0 < 1 − ε`, while `C log(1/ε)/(pε⁴) < 1` for `ε` near `1`); the bound is
   `C (1 + log(1/ε))/(pε⁴)`, which is the printed order for `ε ≤ 1/2`.
3. The statement holds for every number of samples `R` at or above the bound.
4. `MM` is any maximum-matching rule (`IsMaxMatchingRule`), quantified after `C`.
5. Clause (a): every output (any samples inside `E`) is a subgraph of `G` of maximum degree at
   most `R`. Clause (b): `E_{H, Gp} µ(H ∩ Gp) ≥ (1 − ε) E µ(Gp)`, the `R` samples and the test
   realization `T` independent copies of `Gp`. Clause (c): a fixed subgraph `H ⊆ G` with
   `∆(H) ≤ R` and `E µ(H ∩ Gp) ≥ (1 − ε) E µ(Gp)`. `log` is the natural logarithm. -/
theorem theorem_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (p ε : ℝ), 0 < p → p ≤ 1 → 0 < ε → ε < 1 →
    ∀ MM : Finset (Sym2 V) → Finset (Sym2 V), IsMaxMatchingRule G.edgeFinset MM →
    ∀ R : ℕ, C * (1 + Real.log (1 / ε)) / (p * ε ^ 4) ≤ R →
      (∀ S : Fin R → Finset (Sym2 V), (∀ i, S i ⊆ G.edgeFinset) →
        sampleUnion MM S ⊆ G.edgeFinset ∧ ∀ v, degIn (sampleUnion MM S) v ≤ R) ∧
      (1 - ε) * expect (fun _ => p) G.edgeFinset (fun T => (mu T : ℝ)) ≤
        sampleExpect (fun _ => p) G.edgeFinset R
          (fun S => expect (fun _ => p) G.edgeFinset (fun T => (mu (sampleUnion MM S ∩ T) : ℝ))) ∧
      ∃ H ⊆ G.edgeFinset, (∀ v, degIn H v ≤ R) ∧
        (1 - ε) * expect (fun _ => p) G.edgeFinset (fun T => (mu T : ℝ)) ≤
          expect (fun _ => p) G.edgeFinset (fun T => (mu (H ∩ T) : ℝ)) := by sorry

end StochMatchPoly
