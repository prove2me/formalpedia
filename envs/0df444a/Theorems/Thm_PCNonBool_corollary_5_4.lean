-- Prove2me | Theorems.Thm_PCNonBool_corollary_5_4
-- name    : PCNonBool.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:43.364748+00:00
-- url     : https://prove2.me/theorems/3e36cf63-b59d-4544-b1ce-ec25e7ded038
-- title:
--   Corollary 5.4 (corrected: $s \ne 0$, $c \ne 0$) — FPHP$(G)$ needs pigeon degree $> cs/(2\Delta)$
-- statement:
--   **Corollary 5.4.** Let $\mathbb F$ be a field of characteristic different from $2$ and let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander with $s\ne0$, $c\ne0$ and $\Delta>0$. Then every polynomial calculus refutation $\pi$ of FPHP$(G)$ over $\mathbb F$ satisfies
--   $$\mathrm{pdeg}(\pi)\ >\ \frac{c\,s}{2\Delta}.$$
--
--   Applied to the expander $G_\tau$ left at the end of Algorithm 1, this is the lower bound that a small refutation of FPHP$(G)$ would contradict.
--
--   Differences from the source:
--   - correction: the hypotheses of Theorem 5.2 (no condition on s and c) → s ≠ 0 and c ≠ 0; reason: for U = {u}, V = ∅, Δ = 1, (s, c) = (1, 0) or (0, 1), (33b) for u is the empty product 1, so the one-line refutation (1) has pigeon degree 0, not > cs/(2Δ) = 0
--   - encoding: Δ unconstrained → 0 < Δ; reason: cs/(2Δ) is undefined at Δ = 0
--   - reading: no field characteristic stated ("under the hypotheses of Theorem 5.2") → ringChar F ≠ 2; reason: the corollary follows from Fact 5.3, which assumes characteristic ≠ 2, and Section 5 works over such fields; in characteristic 2 the encoding is meaningless (p.26)
--   - generalization: polynomial calculus: axiom lines are axioms of P → an axiom line may be any scalar multiple c·red(a) of a reduced axiom a ∈ P, c = 0 allowed; reason: every standard refutation is one of these, so a lower bound over this larger system implies the paper's; the paper's own Lemmas 5.9 and 5.13 produce scaled axiom lines
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: refutation = derivation of the constant polynomial 1 → IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size or degree
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Corollary 5.4, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_fphp
import Definitions.Def_PCNonBool_pdegSeq

namespace PCNonBool

/-- **Corollary 5.4** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.27 (PDF p.30)), corrected. Under the hypotheses of Theorem
5.2, with `s ≠ 0` and `c ≠ 0`, every polynomial calculus refutation of FPHP(G) over a field of
characteristic `≠ 2` has pigeon degree strictly greater than `cs/(2Δ)`.

**Formalization Note** As printed (any `s`, `c`) the claim fails for `U = {u}`, `V = ∅`, `Δ = 1`,
`(s, c) = (1, 0)` or `(0, 1)`: (33b) for `u` is the empty product `1`, a refutation of pigeon
degree `0`. -/
theorem corollary_5_4 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (s Δ : ℕ) (c : ℝ) (hs : s ≠ 0) (hc : c ≠ 0) (hΔ : 0 < Δ)
    (hG : IsBoundaryExpander G s Δ c) (π : List (MvPolynomial (Var G) F))
    (hπ : IsRefutation redPM (fphp G) π) :
    c * s / (2 * Δ) < (pdegSeq G π : ℝ) := by sorry

end PCNonBool
