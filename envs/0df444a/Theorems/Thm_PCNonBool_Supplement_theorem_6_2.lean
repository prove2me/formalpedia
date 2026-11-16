-- Prove2me | Theorems.Thm_PCNonBool_Supplement_theorem_6_2
-- name    : PCNonBool.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:29:19.83505+00:00
-- url     : https://prove2.me/theorems/07e04434-d7ad-47f0-86c0-caf6d06eac66
-- title:
--   Theorem 6.2 — Col$(G,k)$ needs size $\exp(\Omega((s_0-2\Delta-150|T|)s_1/k^2\Delta^{4\Delta^2}n))$
-- statement:
--   **Theorem 6.2.** There is an absolute constant $\varepsilon>0$ such that the following holds. Let $k\ge3$ be an integer and let $G=(V,E)$ be an $n$-vertex graph with chromatic number strictly greater than $k$. Let $T\subseteq V$ be such that $G[V\setminus T]$ is triangle-free and has maximum degree at most $\Delta$, where $\Delta\ge10$. Suppose that $G$ is $(s_0,\varepsilon_0)$-sparse with $\varepsilon_0\le 1/(3\Delta)$ and $(s_1,\varepsilon_1)$-sparse with $\varepsilon_1\le1/(6\Delta^3)$. Then over every field $\mathbb F$ that contains a primitive $k$-th root of unity, every polynomial calculus refutation $\pi$ of $\mathrm{Col}(G,k)$ has size
--   $$|\pi|\ \ge\ \exp\Bigl(\varepsilon\cdot\frac{(s_0-2\Delta-150|T|)\,s_1}{k^2\,\Delta^{4\Delta^2}\,n}\Bigr).$$
--
--   Lines of the refutation are represented modulo $x_v^k=1$, and size counts monomials. Combined with the sparsity of random graphs, this yields strongly exponential lower bounds for refuting $k$-colourability of random regular and Erdős–Rényi graphs (Corollaries 6.3 and 6.4).
--
--   Differences from the source:
--   - reading: requires size exp(Ω((s0 − 2Δ − 150|T|)s1/k²Δ^{4Δ²}n)) → ∃ ε > 0, chosen before k, G, T, Δ, s0, s1, ε0, ε1, the field and the refutation, with exp(ε·(s0 − 2Δ − 150|T|)s1/(k²Δ^{4Δ²}n)) ≤ |π|; reason: the paper's constant is absolute: its proof, (81) on p.47, gives the exponent ((s0 − 2Δ)/150 − |T|)s1/(600k²(Δ+1)Δ^{3Δ²}n); when the exponent is not positive the bound is trivial, and no positivity hypothesis is added
--   - generalization: polynomial calculus: axiom lines are axioms of the set refuted → the base model PCNonBool.IsDerivation: an axiom line may be any scalar multiple c·red(a) of a reduced axiom a, c = 0 allowed; reason: every standard refutation is one of these, so a lower bound over this larger system implies the paper's
--   - encoding: lines represented in the quotient ring F[x]/⟨x_v^k − 1⟩ (p.11); size = number of monomials → lines are the representatives with individual degrees ≤ k − 1 (redRoot k); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention for lower bounds (p.11), which only strengthens a size lower bound
--   - encoding: refutation = derivation of the constant polynomial 1 → PCNonBool.IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size
--   - encoding: n-vertex graph G = (V, E) with chromatic number > k; G[V ∖ T] triangle-free of maximum degree ≤ Δ; (s, ε)-sparse → SimpleGraph G on a Fintype V, n = Fintype.card V; ¬ G.Colorable k; (G.induce Tᶜ).CliqueFree 3; every v ∉ T has at most Δ neighbours outside T; IsSparse G s ε counts the edges (Sym2) inside U; s0, s1, Δ ∈ ℕ, ε0, ε1 ∈ ℝ; reason: the same notions; the denominator k²Δ^{4Δ²}n is positive since k ≥ 3, Δ ≥ 10 and n ≥ 1
--   - encoding: a field that contains a primitive k-th root of unity → ∃ ξ : F, IsPrimitiveRoot ξ k; reason: the definition
--   - encoding: any field F and any graph → F : Type (universe 0), and the other carriers in Type; reason: Lean convention; the constant precedes the quantifier over fields, so they range over one universe; a refutation over F uses finitely many scalars, hence is a refutation of the same size over the countable subfield they generate, which is isomorphic to a field in Type
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Theorem 6.2, p.34 (PDF p.37); proof (81), p.47 (PDF p.50)

import Mathlib
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_Supplement_redRoot
import Definitions.Def_PCNonBool_Supplement_colAxioms
import Definitions.Def_PCNonBool_Supplement_IsSparse

namespace PCNonBool.Supplement

/-- **Theorem 6.2** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.34 (PDF p.37)). Let `k ≥ 3` be an integer and let `G = (V, E)` be an
`n`-vertex graph with chromatic number strictly greater than `k`. Let `T ⊆ V` be such that
`G[V ∖ T]` is triangle-free and has maximum degree at most `Δ`, where `Δ ≥ 10`. If `G` is
`(s₀, ε₀)`-sparse for `ε₀ ≤ 1/3Δ` and `(s₁, ε₁)`-sparse for `ε₁ ≤ 1/6Δ³`, then over any field that
contains a primitive `k`-th root of unity, every polynomial calculus refutation of `Col(G, k)`
requires size `exp(Ω((s₀ - 2Δ - 150|T|)s₁/k²Δ^{4Δ²}n))`.

**Formalization Note** `exp(Ω(x))` is: one absolute constant `ε > 0`, chosen before `k`, the
graph, `T`, `Δ`, `s₀`, `s₁`, `ε₀`, `ε₁`, the field and the refutation, with `exp(ε x) ≤ |π|`.
Chromatic number `> k` is `¬ G.Colorable k`; the maximum degree of `G[V ∖ T]` is counted among
the vertices outside `T`. Refutations are in the base mission's PC model (`PCNonBool.IsRefutation`):
lines reduced modulo `x_v^k - 1` (`redRoot k`, the paper's convention for lower bounds, p.11),
size = number of monomials of the reduced lines, axiom lines may be scalar multiples of axioms,
and a refutation is a derivation containing `1`. -/
theorem theorem_6_2 : ∃ ε : ℝ, 0 < ε ∧
    ∀ (k : ℕ), 3 ≤ k →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ¬ G.Colorable k →
    ∀ (T : Finset V) (Δ : ℕ),
      (G.induce ((T : Set V)ᶜ)).CliqueFree 3 →
      (∀ v, v ∉ T → (Finset.univ.filter (fun w => w ∉ T ∧ G.Adj v w)).card ≤ Δ) →
      10 ≤ Δ →
    ∀ (s₀ s₁ : ℕ) (ε₀ ε₁ : ℝ),
      IsSparse G s₀ ε₀ → ε₀ ≤ 1 / (3 * (Δ : ℝ)) →
      IsSparse G s₁ ε₁ → ε₁ ≤ 1 / (6 * (Δ : ℝ) ^ 3) →
    ∀ (F : Type) [Field F], (∃ ξ : F, IsPrimitiveRoot ξ k) →
    ∀ π : List (MvPolynomial V F), PCNonBool.IsRefutation (redRoot k) (colAxioms G k) π →
      Real.exp (ε * (((s₀ : ℝ) - 2 * (Δ : ℝ) - 150 * (T.card : ℝ)) * (s₁ : ℝ) /
          ((k : ℝ) ^ 2 * (Δ : ℝ) ^ (4 * Δ ^ 2) * (Fintype.card V : ℝ)))) ≤
        (PCNonBool.pcSize π : ℝ) := by sorry

end PCNonBool.Supplement
