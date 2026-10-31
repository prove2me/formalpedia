-- Prove2me | Theorems.Thm_TractableComposite_theorem_2_facet_generation
-- name    : TractableComposite.theorem_2_facet_generation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:55:55.744997+00:00
-- url     : https://prove2.me/theorems/306e956c-8399-4afe-bc72-cc13da67abc7
-- title:
--   Theorem 2 — a facet of $\operatorname{conc}_P(\bar\phi)$ tight at $\bar u$ in $O(dn\log d)$ operations
-- statement:
--   Let $d,n\ge1$, let $a\in\mathbb R^{d\times(n+1)}$ have strictly increasing rows, let $\phi:\mathbb R^d\to\mathbb R$ be continuous and $\bar\phi(u)=\phi(u_{1n},\dots,u_{dn})$. Assume $\bar\phi$ is concave-extendable from $\operatorname{vert}(Q)$ and supermodular on the vertices of $Q$. There is a constant $C$, independent of $d,n,a,\phi$ and the input, such that for every $\bar u\in P$ the facet-generation program (lift $\bar u$ to $\bar s$, compute $J$, run Algorithm 1 at $\bar s$, return $(\Gamma_J^{\top}\alpha^\pi,b^\pi)$):
--
--   1. stops after at most $C\,d\,n\,(\lfloor\log_2d\rfloor+1)$ ticks, and
--   2. returns $(\alpha',b')$ such that
--
--   $$\phi\le\langle\alpha',u\rangle+b'$$
--
--   is a facet-defining inequality of $\operatorname{conc}_P(\bar\phi)$ that is tight at $\bar u$.
--
--   The ticks count unit-cost real arithmetic, comparisons and queries of $\phi$. This is the facet-generation (separation) step for the concave envelope of a supermodular, concave-extendable outer-function over $P$, a problem that is NP-hard without these assumptions.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - generalization: 0 ≤ a_i0 < ⋯ < a_in ≤ 1 (normalization of (1)) → any strictly increasing rows a_i; reason: the paper's normalization is without loss of generality (p.3) and §3.1 never uses the bounds; every normalized a is an instance
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain
--   - reading: Algorithm 1 / "can be found" → the explicit program alg1Prog (resp. facetGen, liftProg) that the proof describes; reason: the statement is about the paper's algorithm, written as a program; its output is the inequality
--   - reading: O(dn log d) operations → ∃ C chosen before d, n, a, φ and the input, with ticks ≤ C·d·n·(⌊log₂ d⌋ + 1); reason: log₂ 1 = 0 would make the bound 0 at d = 1; for d ≥ 2, ⌊log₂ d⌋ + 1 ≤ 2 log₂ d, so the bound is the paper's
--   - reading: operations (no machine model named) → ticks of the published real-RAM model LNTopology.Hermetization.tick: unit-cost real arithmetic, comparisons and φ queries, every loop iteration ticks; reason: the paper counts (15), which needs dn + 1 values of φ, as O(dn), so arithmetic and φ values are unit cost
--   - reading: Algorithm 1 lines 5–6: z̄_i0 first; equal z_ij, z_ij+1 adjacent in the sorted order → the sort merges rows with ties to the smaller i, keeping each row's order of j; reason: a concrete sort satisfying lines 5–6 by construction
--   - reading: facet-defining inequality (non-vertical) of an envelope, tight at a point → IsTightFacet: valid on the domain, the point in the tight set, dim of the tight set = dim of the domain; reason: the paper's notion: the proofs of Corollary 2 and Theorem 2 compare dim T^{(α,b)} with the dimension of the domain; non-verticality is automatic for φ ≤ ⟨α,u⟩ + b
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Theorem 2, p.14 (proof, p.14)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_TractableComposite_ip
import Definitions.Def_TractableComposite_phiBar
import Definitions.Def_TractableComposite_P
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_vertQ
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_ConcaveExtendable
import Definitions.Def_TractableComposite_IsTightFacet
import Definitions.Def_TractableComposite_facetGen

namespace TractableComposite

/-- **Theorem 2**, p.14. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Theorem 2, p.14 (proof, p.14).

Assume that `φ̄` is concave-extendable from vert(Q) and is supermodular when restricted to the vertices of
`Q`. Let `ū ∈ P`. Then a facet-defining inequality of `conc_P(φ̄)` which is tight at `ū` can be found in
`O(dn log d)` operations.

**Formalization Note.**
* "Can be found" is stated for the explicit program `facetGen` of the paper's proof (lift `ū` to `s̄`,
  compute `J`, run Algorithm 1 at `s̄`, return `(Γ_Jᵀα^π, b^π)`), in the published real-RAM tick model
  (reading R3: unit-cost real operations, comparisons and `φ` queries; every loop iteration ticks).
* Reading R2: "O(dn log d)" is `∃ C`, chosen before `d, n, a, φ, ū`, with ticks
  `≤ C·d·n·(⌊log₂ d⌋ + 1)`.
* Reading R5: the output `(α', b')` satisfies `IsTightFacet` for `conc_P(φ̄)` and `u ↦ ⟨α',u⟩ + b'`: valid on
  `P`, tight at `ū`, and the tight set has the dimension of `P`; non-verticality is automatic.
* Reading R4: the tie rule of Algorithm 1 (lines 5–6) is built into the merge.
* Reading R9: any strictly increasing rows `aᵢ` (no normalization to `[0,1]`); `φ` continuous (p.3). -/
theorem theorem_2_facet_generation :
    ∃ C : ℕ, ∀ (d n : ℕ), 1 ≤ d → 1 ≤ n → ∀ a : Fin d → Fin (n + 1) → ℝ, (∀ i, StrictMono (a i)) →
      ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ →
      ConcaveExtendable (Q a) (vertQ a) (phiBar φ) →
      Supermodularity.Monotonicity.SupermodularOn (phiBar φ) (vertQ a) →
      ∀ u ∈ P a,
        ((facetGen a φ u).run 0).2 ≤ C * d * n * (Nat.log 2 d + 1) ∧
        IsTightFacet (P a) (concOn (P a) (phiBar φ))
          (fun u' => ip ((facetGen a φ u).run 0).1.1 u' + ((facetGen a φ u).run 0).1.2) u := by sorry

end TractableComposite
