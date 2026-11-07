-- Prove2me | Theorems.Thm_PCNonBool_theorem_5_1
-- name    : PCNonBool.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:14.367759+00:00
-- url     : https://prove2.me/theorems/92a18e04-95e3-4cbb-8495-fa4750b0544f
-- title:
--   Theorem 5.1 — FPHP$(G)$ on an $(s,\Delta,c)$-boundary expander with $c \ge 5$ needs refutations of size $\exp(\Omega((c-1)s^2/\Delta^3 N))$
-- statement:
--   **Theorem 5.1.** There is an absolute constant $\varepsilon>0$ such that the following holds. Let $\mathbb F$ be any field of characteristic different from $2$, and let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander with $c\ge5$, $|V|=n$ and $|U|=N>n$. Then every polynomial calculus refutation $\pi$ of the functional pigeonhole principle FPHP$(G)$ over $\mathbb F$ has size
--   $$|\pi|\ \ge\ \exp\Bigl(\varepsilon\cdot\frac{(c-1)\,s^2}{\Delta^3 N}\Bigr),$$
--   that is, polynomial calculus requires size $\exp(\Omega((c-1)s^2/\Delta^3N))$ to refute FPHP$(G)$.
--
--   FPHP$(G)$ is encoded over $\pm1$-valued variables ($x_{i,j}=-1$ iff pigeon $i$ flies to hole $j$), which is the Fourier basis; lines of a refutation are represented modulo $x_{i,j}^2=1$ and size counts monomials. Since boundary expanders with $c\ge5$, $\Delta=O(1)$ and $s=\Omega(n)$ exist when $N=O(n)$, this gives $\exp(\Omega(n))$ size lower bounds, which the paper notes are optimal up to the constant in the exponent.
--
--   Differences from the source:
--   - reading: "requires size exp(Ω((c − 1)s²/Δ³N))" → ∃ ε > 0, chosen before the field, the graph, s, Δ, c and the refutation, with exp(ε·(c − 1)s²/(Δ³N)) ≤ |π|; reason: the paper's constant is absolute (its proof gives ε of order 1/1200 via Dτ/(2ΔN), D = (c − 1)s/(12Δ), τ = s/(10(2Δ + 3))); this is equivalent to the threshold reading of Ω, since whenever the exponent is positive every refutation has size ≥ 2
--   - generalization: polynomial calculus: axiom lines are axioms of P → an axiom line may be any scalar multiple c·red(a) of a reduced axiom a ∈ P, c = 0 allowed; reason: every standard refutation is one of these, so a lower bound over this larger system implies the paper's; the paper's own Lemmas 5.9 and 5.13 produce scaled axiom lines
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: refutation = derivation of the constant polynomial 1 → IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size or degree
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
--   - encoding: s, Δ, c of the expander; |U| = N, |V| = n → s, Δ ∈ ℕ, c ∈ ℝ; N = Fintype.card U, n = Fintype.card V; at Δ = 0 Lean's x/0 = 0 makes the bound exp(0) = 1; reason: at Δ = 0 the paper's expression is undefined; there s ≥ 1 and c ≥ 5 force U = ∅, which N > n excludes, so only s = 0 remains, where the bound is 1 in both readings
--   - encoding: any field F, any bipartite graph → F, U, V : Type (universe 0); reason: Lean convention; ε precedes the quantifier over fields, so they range over one universe; no instance is lost, since every finite graph is isomorphic to one in Type, and a refutation over F uses finitely many scalars, so it is a refutation of the same size over the countable subfield they generate, which is isomorphic to a field in Type
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Theorem 5.1, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_pcSize
import Definitions.Def_PCNonBool_fphp

namespace PCNonBool

/-- **Theorem 5.1** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.26 (PDF p.29)). If `G = (U ⊔ V, E)` is an `(s, Δ, c)`-boundary
expander for `c ≥ 5`, where `|V| = n` and `|U| = N > n`, then every polynomial calculus refutation
of FPHP(G) over any field of characteristic different from 2 requires size
`exp(Ω((c - 1)s²/Δ³N))`.

**Formalization Note** `exp(Ω(x))` is: there is one absolute constant `ε > 0`, chosen before the
field, the graph, `s`, `Δ`, `c` and the refutation, with `exp(ε x) ≤ |π|`. Refutations are in the
mission's PC model: lines reduced modulo the range axioms `x² - 1` (the paper's convention, p.11),
size = number of monomials of the reduced lines, fan-in 2, axiom lines may be scalar multiples of
axioms (a larger system than the paper's, so the bound is at least as strong), and a refutation is
a derivation containing `1`. -/
theorem theorem_5_1 : ∃ ε : ℝ, 0 < ε ∧
    ∀ (F : Type) [Field F], ringChar F ≠ 2 →
    ∀ (U V : Type) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (G : BipGraph U V)
      (s Δ : ℕ) (c : ℝ), 5 ≤ c → Fintype.card V < Fintype.card U →
      IsBoundaryExpander G s Δ c →
      ∀ π : List (MvPolynomial (Var G) F), IsRefutation redPM (fphp G) π →
        Real.exp (ε * ((c - 1) * (s : ℝ) ^ 2 / ((Δ : ℝ) ^ 3 * (Fintype.card U : ℝ)))) ≤
          (pcSize π : ℝ) := by sorry

end PCNonBool
