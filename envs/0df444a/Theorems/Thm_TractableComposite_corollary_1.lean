-- Prove2me | Theorems.Thm_TractableComposite_corollary_1
-- name    : TractableComposite.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:54:27.860268+00:00
-- url     : https://prove2.me/theorems/8b450066-b296-4b7a-9c22-72ba56f7e694
-- title:
--   Corollary 1 — Algorithm 1 finds a facet of $\operatorname{conc}_Q(\bar\phi)$ tight at $\bar s$ in $O(dn\log d)$ operations
-- statement:
--   There is a constant $C$ such that the following holds for all $d,n\ge1$, all $a$ with strictly increasing rows and all continuous $\phi$ for which $\bar\phi$ is concave-extendable from $\operatorname{vert}(Q)$ and supermodular on $\operatorname{vert}(Q)$. For every $\bar s\in Q$, the program of Algorithm 1
--
--   1. stops after at most $C\,d\,n\,(\lfloor\log_2d\rfloor+1)$ ticks, and
--   2. returns $(\alpha,b)$ such that $\phi\le\langle\alpha,s\rangle+b$ is a facet-defining inequality of $\operatorname{conc}_Q(\bar\phi)$ tight at $\bar s$.
--
--   The ticks count unit-cost real arithmetic, comparisons and queries of $\phi$.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain
--   - reading: Algorithm 1 / "can be found" → the explicit program alg1Prog (resp. facetGen, liftProg) that the proof describes; reason: the statement is about the paper's algorithm, written as a program; its output is the inequality
--   - reading: O(dn log d) operations → ∃ C chosen before d, n, a, φ and the input, with ticks ≤ C·d·n·(⌊log₂ d⌋ + 1); reason: log₂ 1 = 0 would make the bound 0 at d = 1; for d ≥ 2, ⌊log₂ d⌋ + 1 ≤ 2 log₂ d, so the bound is the paper's
--   - reading: operations (no machine model named) → ticks of the published real-RAM model LNTopology.Hermetization.tick: unit-cost real arithmetic, comparisons and φ queries, every loop iteration ticks; reason: the paper counts (15), which needs dn + 1 values of φ, as O(dn), so arithmetic and φ values are unit cost
--   - reading: Algorithm 1 lines 5–6: z̄_i0 first; equal z_ij, z_ij+1 adjacent in the sorted order → the sort merges rows with ties to the smaller i, keeping each row's order of j; reason: a concrete sort satisfying lines 5–6 by construction
--   - reading: facet-defining inequality (non-vertical) of an envelope, tight at a point → IsTightFacet: valid on the domain, the point in the tight set, dim of the tight set = dim of the domain; reason: the paper's notion: the proofs of Corollary 2 and Theorem 2 compare dim T^{(α,b)} with the dimension of the domain; non-verticality is automatic for φ ≤ ⟨α,u⟩ + b
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Corollary 1, p.12 (proof, p.13)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_TractableComposite_ip
import Definitions.Def_TractableComposite_phiBar
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_vertQ
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_ConcaveExtendable
import Definitions.Def_TractableComposite_IsTightFacet
import Definitions.Def_TractableComposite_alg1Prog

namespace TractableComposite

/-- **Corollary 1**, p.12. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Corollary 1, p.12 (proof, p.13).

If `φ̄` is concave-extendable from vert(Q) and supermodular on the vertices of `Q`, then, given `s̄ ∈ Q`,
Algorithm 1 takes `O(dn log d)` operations to find a non-vertical facet-defining inequality of
`conc_Q(φ̄)(·)` which is tight at `s̄`.

**Formalization Note.** Algorithm 1 is the explicit program `alg1Prog` in the published real-RAM tick
model (reading R3: unit-cost real operations, comparisons and `φ` queries). Reading R2: "O(dn log d)"
is `∃ C`, chosen before `d, n, a, φ, s̄`, with ticks `≤ C·d·n·(⌊log₂ d⌋ + 1)` (the `+1` keeps the bound
meaningful at `d = 1`). Reading R5: the output `(α, b)` satisfies `IsTightFacet` for `conc_Q(φ̄)` and
`s ↦ ⟨α,s⟩ + b` (valid on `Q`, tight at `s̄`, tight set of dimension `dim Q`); non-verticality is automatic. -/
theorem corollary_1 :
    ∃ C : ℕ, ∀ (d n : ℕ), 1 ≤ d → 1 ≤ n → ∀ a : Fin d → Fin (n + 1) → ℝ, (∀ i, StrictMono (a i)) →
      ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ →
      ConcaveExtendable (Q a) (vertQ a) (phiBar φ) →
      Supermodularity.Monotonicity.SupermodularOn (phiBar φ) (vertQ a) →
      ∀ s ∈ Q a,
        ((alg1Prog a φ s).run 0).2 ≤ C * d * n * (Nat.log 2 d + 1) ∧
        IsTightFacet (Q a) (concOn (Q a) (phiBar φ))
          (fun s' => ip ((alg1Prog a φ s).run 0).1.1 s' + ((alg1Prog a φ s).run 0).1.2) s := by sorry

end TractableComposite
