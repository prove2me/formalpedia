-- Prove2me | Theorems.Thm_PCNonBool_theorem_5_2
-- name    : PCNonBool.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:31.088536+00:00
-- url     : https://prove2.me/theorems/c1d2b27d-7ea1-4b35-901c-0daa2f0347da
-- title:
--   Theorem 5.2 ([MN24], Theorem 5.8) (corrected: $s \ne 0$, $c \ne 0$) — FPHP$(G)_{\mathrm{bool}}$ needs pigeon degree $> cs/(2\Delta)$
-- statement:
--   **Theorem 5.2** (Mikša–Nordström [MN24], Theorem 5.8, as cited). Let $\mathbb F$ be any field and let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander with $s\ne0$, $c\ne0$ and $\Delta>0$. Then every polynomial calculus refutation $\pi$ of the Boolean encoding FPHP$(G)_{\mathrm{bool}}$ has pigeon degree
--   $$\mathrm{pdeg}(\pi)\ >\ \frac{c\,s}{2\Delta}.$$
--
--   This is the degree lower bound from which the size lower bound of Theorem 5.1 is eventually derived, after transfer to the $\pm1$ encoding (Fact 5.3).
--
--   **Formalization Note** Lines are kept modulo $x^2-x$. Pigeon degree of a refutation is the largest number of pigeons mentioned by a monomial of a line.
--
--   Differences from the source:
--   - correction: no condition on s and c → s ≠ 0 and c ≠ 0; reason: the printed statement is false for U = {u}, V = ∅, Δ = 1, (s, c) = (1, 0) or (0, 1): the graph is an (s, Δ, c)-boundary expander, (34b) for u is −1, and the refutation (−1, 1) has pigeon degree 0, not > cs/(2Δ) = 0
--   - encoding: Δ unconstrained → 0 < Δ; reason: cs/(2Δ) is undefined at Δ = 0 (Lean's x/0 = 0 would make it a different, false claim)
--   - generalization: polynomial calculus: axiom lines are axioms of P → an axiom line may be any scalar multiple c·red(a) of a reduced axiom a ∈ P, c = 0 allowed; reason: every standard refutation is one of these, so a lower bound over this larger system implies the paper's; the paper's own Lemmas 5.9 and 5.13 produce scaled axiom lines
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: refutation = derivation of the constant polynomial 1 → IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size or degree
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Theorem 5.2 ([MN24], Theorem 5.8), p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_redBool
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_fphpBool
import Definitions.Def_PCNonBool_pdegSeq

namespace PCNonBool

/-- **Theorem 5.2** ([MN24], Theorem 5.8) (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.26 (PDF p.29)), corrected. If `G` is an
`(s, Δ, c)`-boundary expander with `s ≠ 0` and `c ≠ 0`, then every polynomial calculus refutation
of FPHP(G)_bool, over any field, has pigeon degree strictly greater than `cs/(2Δ)`.

**Formalization Note** Correction: as printed (any `s`, `c`) the statement is false: for `U = {u}`,
`V = ∅`, `Δ = 1` and `(s, c) = (1, 0)` or `(0, 1)`, the graph is an `(s, Δ, c)`-boundary expander,
(34b) for `u` is the empty sum minus one, `-1`, and `(-1, 1)` is a refutation of pigeon degree
`0`, which is not `> cs/(2Δ) = 0`. `0 < Δ` makes `cs/(2Δ)` defined. Lines are reduced modulo
`x² - x` (`redBool`); axiom lines may be scalar multiples of axioms. -/
theorem theorem_5_2 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s Δ : ℕ) (c : ℝ) (hs : s ≠ 0) (hc : c ≠ 0) (hΔ : 0 < Δ)
    (hG : IsBoundaryExpander G s Δ c) (π : List (MvPolynomial (Var G) F))
    (hπ : IsRefutation redBool (fphpBool G) π) :
    c * s / (2 * Δ) < (pdegSeq G π : ℝ) := by sorry

end PCNonBool
