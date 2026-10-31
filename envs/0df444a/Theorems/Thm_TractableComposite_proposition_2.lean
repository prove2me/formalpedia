-- Prove2me | Theorems.Thm_TractableComposite_proposition_2
-- name    : TractableComposite.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:53:16.174338+00:00
-- url     : https://prove2.me/theorems/286a3ce4-3d9a-4fa5-ba67-7f7c01e52804
-- title:
--   Proposition 2 (Cor. 2 in [17]) — lift in $O(dn)$ and extend a facet of $\operatorname{conc}_{Q_J}$ to one of $\operatorname{conc}_P$
-- statement:
--   Assume $\operatorname{conc}_Q(\bar\phi)$ is a polyhedral function. Given $\bar u\in P$:
--
--   1. the unique lifting $(\bar u,\bar s)\in PQ'$ is computed by the monotone-chain program in at most $C\,dn$ ticks, for a constant $C$ chosen before the input;
--   2. with $J_i=\{j\mid\bar u_{ij}=\bar s_{ij}\}$, $\bar s\in F_J$ and $\bar s_J\in Q_J$;
--   3. if $\phi\le\langle\alpha_J,s_J\rangle+b$ is a facet-defining inequality of $\operatorname{conc}_{Q_J}(\bar\phi)$ tight at $\bar s_J$, then $\phi\le\langle(\alpha_J,0),(u_J,u_{\bar J})\rangle+b$ is a facet-defining inequality of $\operatorname{conc}_P(\bar\phi)$ tight at $\bar u$.
--
--   This reduces facet generation over $P$ to facet generation over a projection of a face of $Q$.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - generalization: 0 ≤ a_i0 < ⋯ < a_in ≤ 1 (normalization of (1)) → any strictly increasing rows a_i; reason: the paper's normalization is without loss of generality (p.3) and §3.1 never uses the bounds; every normalized a is an instance
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain
--   - encoding: conc_Q(φ̄) is a polyhedral function → IsPolyhedralOn: finitely many affine majorants on Q, one of which equals the envelope at each point; reason: a concave function on a polytope is polyhedral iff it is the minimum of finitely many affine functions on it
--   - encoding: y_J ∈ ℝ^{|J₁|+⋯+|J_d|} → (i : Fin d) → J i → ℝ (block i indexed by the subtype J i); reason: Lean convention; same points
--   - reading: operations (no machine model named) → ticks of the published real-RAM model LNTopology.Hermetization.tick: unit-cost real arithmetic, comparisons and φ queries, every loop iteration ticks; reason: the paper counts (15), which needs dn + 1 values of φ, as O(dn), so arithmetic and φ values are unit cost
--   - reading: Algorithm 1 / "can be found" → the explicit program alg1Prog (resp. facetGen, liftProg) that the proof describes; reason: the statement is about the paper's algorithm, written as a program; its output is the inequality
--   - reading: can be found in O(dn) time → ∃ C chosen before the input with ticks of liftProg ≤ C·d·n, and its output equals the lifting s̄; reason: same reading of a time bound as R2; PQ' is the graph of ū ↦ s̄, so the output equal to s̄ is the uniqueness clause
--   - reading: conc_{Q_J}(φ) → the envelope of φ̄ (on Q_J: y ↦ φ(y₁ₙ,…,y_dn)); reason: φ ↔ φ̄ typo: φ is defined on ℝ^d, the envelope is over a subset of ℝ^{d×(n+1)}
--   - reading: facet-defining inequality (non-vertical) of an envelope, tight at a point → IsTightFacet: valid on the domain, the point in the tight set, dim of the tight set = dim of the domain; reason: the paper's notion: the proofs of Corollary 2 and Theorem 2 compare dim T^{(α,b)} with the dimension of the domain; non-verticality is automatic for φ ≤ ⟨α,u⟩ + b
--   - encoding: conc(ξᵢ)(aᵢⱼ; ūᵢ), the concave envelope of the discrete function ξᵢ at aᵢⱼ → liftS: supremum of ∑ₖ wₖ ūᵢₖ over weights w ≥ 0 with ∑ₖ wₖ = 1 and ∑ₖ wₖ aᵢₖ = aᵢⱼ; reason: ξᵢ is −∞ off the points aᵢₖ, so only convex combinations of those points count; same values
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Proposition 2, p.6

import Mathlib
import Definitions.Def_TractableComposite_ip
import Definitions.Def_TractableComposite_phiBar
import Definitions.Def_TractableComposite_P
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_IsTightFacet
import Definitions.Def_TractableComposite_FJ
import Definitions.Def_TractableComposite_QJ
import Definitions.Def_TractableComposite_restrictJ
import Definitions.Def_TractableComposite_padJ
import Definitions.Def_TractableComposite_phiBarJ
import Definitions.Def_TractableComposite_liftS
import Definitions.Def_TractableComposite_Jof
import Definitions.Def_TractableComposite_IsPolyhedralOn
import Definitions.Def_TractableComposite_liftProg

namespace TractableComposite

/-- **Proposition 2 (Corollary 2 in [17])**, p.6. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Proposition 2, p.6.

Assume `conc_Q(φ̄)` is a polyhedral function. Given `ū ∈ P`, the unique point `(ū, s̄) ∈ PQ'` can be found in
`O(dn)` time. Let `Jᵢ = {j | ūᵢⱼ = s̄ᵢⱼ}`. Then `s̄ ∈ F_J` and `s̄_J ∈ Q_J`. If `φ ≤ ⟨α_J, s_J⟩ + b` is a
facet-defining inequality for `conc_{Q_J}(φ̄)` that is tight at `s̄_J`, then `φ ≤ ⟨(α_J, 0), (u_J, u_J̄)⟩ + b`
defines a facet of `conc_P(φ̄)` that is tight at `ū`.

**Formalization Note.** The lifting is computed by the explicit program `liftProg` (monotone-chain upper
hull, pp.4–5) in the published real-RAM tick model (reading R3); "can be found in O(dn) time" is
`∃ C` (chosen before the input) with ticks `≤ C·d·n` and output equal to `s̄ = liftS a ū`; `PQ'` (4) is the
graph of `ū ↦ s̄`, so the output being `s̄` is the uniqueness clause. Reading R7: `conc_{Q_J}(φ)` is the
envelope of `φ̄` on `Q_J` (`phiBarJ`). `⟨(α_J,0), u⟩ = ⟨padJ J α_J, u⟩`. Reading R5 for "facet". -/
theorem proposition_2 :
    ∃ C : ℕ, ∀ (d n : ℕ), 1 ≤ d → 1 ≤ n → ∀ a : Fin d → Fin (n + 1) → ℝ, (∀ i, StrictMono (a i)) →
      ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ →
      IsPolyhedralOn (Q a) (concOn (Q a) (phiBar φ)) →
      ∀ u ∈ P a,
        ((liftProg a u).run 0).2 ≤ C * d * n ∧
        ((liftProg a u).run 0).1 = liftS a u ∧
        liftS a u ∈ FJ a (Jof a u) ∧
        restrictJ (Jof a u) (liftS a u) ∈ QJ a (Jof a u) ∧
        ∀ (αJ : (i : Fin d) → Jof a u i → ℝ) (b : ℝ),
          IsTightFacet (QJ a (Jof a u)) (concOn (QJ a (Jof a u)) (phiBarJ φ (Jof a u)))
              (fun y => ip αJ y + b) (restrictJ (Jof a u) (liftS a u)) →
            IsTightFacet (P a) (concOn (P a) (phiBar φ))
              (fun u' => ip (padJ (Jof a u) αJ) u' + b) u := by sorry

end TractableComposite
