-- Prove2me | Theorems.Thm_TractableComposite_lemma_3
-- name    : TractableComposite.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:54.514986+00:00
-- url     : https://prove2.me/theorems/11cd6441-1feb-401b-93e7-7dc8efdf4750
-- title:
--   Lemma 3 (Lemma 8 in [17]) — envelopes over $F_J$ and $Q_J$ agree, and their tight sets are affinely isomorphic
-- statement:
--   Assume $\operatorname{conc}_Q(\bar\phi)$ is polyhedral and let $J\in\mathcal J$. Then
--
--   1. $\operatorname{conc}_{F_J}(\bar\phi)(s)=\operatorname{conc}_{Q_J}(\bar\phi)(s_J)$ for every $s\in F_J$;
--   2. if $\phi\le\langle\alpha,s\rangle+b$ is valid for $\operatorname{conc}_Q(\bar\phi)$ on $Q$ and $\alpha_{\bar J}=0$, then the affine map $A$ of (18) maps the tight set $T^{(\alpha_J,b)}_{\bar\phi}(Q_J)$ bijectively onto $T^{(\alpha,b)}_{\bar\phi}(F_J)$.
--
--   Here $T^{(\alpha,b)}_f(X)=\{x\in X\mid\operatorname{conc}_X(f)(x)=\langle\alpha,x\rangle+b\}$.
--
--   Differences from the source:
--   - encoding: indices i ∈ {1,…,d}, j ∈ {0,…,n}; points of ℝ^{d×(n+1)} → Fin d, Fin (n+1) (0-based, same j); Fin d → Fin (n+1) → ℝ; reason: Lean convention; same instances
--   - encoding: d, n positive integers ("Let n ∈ Z", p.3) → 1 ≤ d, 1 ≤ n; reason: "n ∈ Z" is a typo for a positive integer; the paper's setting
--   - encoding: concave envelope conc_D(g), and conc_D(g|_X) → concOn: supremum over finite convex combinations of points of D (resp. X); reason: the concave envelope of a function on a convex set; same values at every point of the domain
--   - encoding: conc_Q(φ̄) is a polyhedral function → IsPolyhedralOn: finitely many affine majorants on Q, one of which equals the envelope at each point; reason: a concave function on a polytope is polyhedral iff it is the minimum of finitely many affine functions on it
--   - encoding: y_J ∈ ℝ^{|J₁|+⋯+|J_d|} → (i : Fin d) → J i → ℝ (block i indexed by the subtype J i); reason: Lean convention; same points
--   - encoding: φ̄ evaluated at a point s_J of Q_J → phiBarJ φ J y = φ(y₁ₙ,…,y_dn), reading coordinate n ∈ Jᵢ of each block; reason: φ̄ depends only on the coordinates sᵢₙ and n ∈ Jᵢ for J ∈ 𝒥, so this is φ̄ of every point whose J-restriction is y
--   - encoding: the tight sets are affinely isomorphic under A → A maps the Q_J tight set onto the F_J tight set and is injective on it; reason: A is affine by construction; a bijection by an affine map is an affine isomorphism
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Lemma 3, p.14; (18), pp.13–14

import Mathlib
import Definitions.Def_TractableComposite_ip
import Definitions.Def_TractableComposite_phiBar
import Definitions.Def_TractableComposite_Q
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_TractableComposite_IsJTuple
import Definitions.Def_TractableComposite_FJ
import Definitions.Def_TractableComposite_QJ
import Definitions.Def_TractableComposite_restrictJ
import Definitions.Def_TractableComposite_AmapJ
import Definitions.Def_TractableComposite_phiBarJ
import Definitions.Def_TractableComposite_IsPolyhedralOn

namespace TractableComposite

/-- **Lemma 3 (Lemma 8 in [17])**, p.14. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), Lemma 3, p.14; the map `A` of (18), pp.13–14.

Assume `conc_Q(φ̄)` is a polyhedral function and `J ∈ 𝒥`. Then `conc_{F_J}(φ̄)(s) = conc_{Q_J}(φ̄)(s_J)` for every
`s ∈ F_J`. Let `φ ≤ ⟨α, s⟩ + b` be a valid inequality of `conc_Q(φ̄)` with `α_J̄ = 0`. Then the tight sets
`T^{(α,b)}_φ̄(F_J)` and `T^{(α_J,b)}_φ̄(Q_J)` are affinely isomorphic under the affine map `A` of (18).

**Formalization Note.** `φ̄` on `Q_J` is `y ↦ φ(y₁ₙ, …, y_dn)` (`phiBarJ`). The tight sets are
`{s ∈ F_J | conc_{F_J}(φ̄)(s) = ⟨α,s⟩ + b}` and `{y ∈ Q_J | conc_{Q_J}(φ̄)(y) = ⟨α_J,y⟩ + b}` (p.12). "Affinely
isomorphic under `A`" is: `A` (an affine map by construction) maps the second set onto the first and is
injective on it. `φ` continuous (p.3). -/
theorem lemma_3 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (a : Fin d → Fin (n + 1) → ℝ) (ha : ∀ i, StrictMono (a i)) (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ)
    (hpoly : IsPolyhedralOn (Q a) (concOn (Q a) (phiBar φ)))
    (J : Fin d → Finset (Fin (n + 1))) (hJ : IsJTuple J) :
    (∀ s ∈ FJ a J, concOn (FJ a J) (phiBar φ) s = concOn (QJ a J) (phiBarJ φ J) (restrictJ J s)) ∧
    ∀ (α : Fin d → Fin (n + 1) → ℝ) (b : ℝ), (∀ s ∈ Q a, concOn (Q a) (phiBar φ) s ≤ ip α s + b) →
      (∀ i j, j ∉ J i → α i j = 0) →
      AmapJ a J '' {y ∈ QJ a J | concOn (QJ a J) (phiBarJ φ J) y = ip (restrictJ J α) y + b} =
          {s ∈ FJ a J | concOn (FJ a J) (phiBar φ) s = ip α s + b} ∧
        Set.InjOn (AmapJ a J)
          {y ∈ QJ a J | concOn (QJ a J) (phiBarJ φ J) y = ip (restrictJ J α) y + b} := by sorry

end TractableComposite
