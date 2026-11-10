-- Prove2me | Theorems.Thm_VAS5Reach_proposition_6_2
-- name    : VAS5Reach.proposition_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:34.961172+00:00
-- url     : https://prove2.me/theorems/9a56b48f-2f8b-4e13-942b-aaa03ecee2e0
-- title:
--   Proposition 6.2 — Case I instances satisfy $\ell_{V'}(s',t') \le (B + \mathrm{SIZE}(V',s',t'))^{O(1)}$
-- statement:
--   There is a constant $c$ with the following property. Let $V''$ be a 5-VASS, $I_1, I_2 \subseteq [5]$ sets of two coordinates and $B \in \mathbb N$, with $\dim_{\mathrm{cyc}}(\widehat{[\![V'']\!]}_{I_i,B}) \le 2$ for $i = 1, 2$, and let $V'$ be $\widehat{[\![V'']\!]}_{I_1,B}$ and $\widehat{[\![V'']\!]}_{I_2,B}$ connected by a zero-effect transition $(r_1(u_1), 0, r_2(u_2))$ from the first to the second, with source $s' = (p, s{\restriction}_{I_1})(s)$ and target $t' = (q, t{\restriction}_{I_2})(t)$. If $s' \xrightarrow{*} t'$ in $V'$, then
--   $$
--   \ell_{V'}(s', t') \le \bigl(B + \mathrm{SIZE}(V', s', t')\bigr)^{c}.
--   $$
--   Together with Theorem 6.1 this settles Case I of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - reading: every reachable instance (V′, s′, t′) in Case I → V′ built from a 5-VASS V″, I₁, I₂, B by the construction of Theorem 6.1 I (both cycle-dimensions ≤ 2, s′ = (p, s↾I₁)(s), t′ = (q, t↾I₂)(t)), without the size bound on V″; reason: p.25: 'consider the reachable instance (V′, s′, t′) obtained from V″ by the construction in Case I'
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §6.1 and Proposition 6.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_cycleSpace
import Definitions.Def_VAS5Reach_VASS_bridgeUnion

namespace VAS5Reach

/-- **Proposition 6.2.** Every reachable instance `(V′, s′, t′)` in Case I satisfies
`ℓ_{V′}(s′, t′) ≤ (B + SIZE(V′, s′, t′))^{O(1)}`.

Here, as fixed before the proposition, `V″` is a 5-VASS, `I₁, I₂ ⊆ [5]` contain two elements,
`B ∈ ℕ`, and `(V′, s′, t′)` is obtained from `V″` by the construction of Case I of Theorem 6.1:
`V′` is `[[V″]]^_{I₁,B}` and `[[V″]]^_{I₂,B}`, both of cycle-dimension at most `2`, connected by
a zero-effect transition `(r₁(u₁), 0, r₂(u₂))` from the first to the second, and
`s′ = (p, s↾I₁)(s)`, `t′ = (q, t↾I₂)(t)`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §6.1, printed p. 25 (PDF p. 27): "we fix a 5-VASS V″, I1, I2 ⊆ [5] containing
two elements, and B ∈ N, and consider the reachable instance (V′, s′, t′) obtained from V″ by the
construction in Case I", and Proposition 6.2, printed p. 25 (PDF p. 27).

**Formalization Note** The size bound on `V″` of Theorem 6.1 is not a hypothesis (it is not part
of "in Case I"). `ℓ_{V′}(s′, t′) ≤ N` is stated as a run of `V′` of length `≤ N`. `O(1)` is one
constant `c` quantified before every instance. -/
theorem proposition_6_2 :
    ∃ c : ℕ, ∀ (Q : Type) (V'' : VASS Q (Fin 5)) (I₁ I₂ : Finset (Fin 5)) (B : ℕ) (p q : Q)
      (r₁ : Q × (I₁ → ℕ)) (r₂ : Q × (I₂ → ℕ)) (s t : Fin 5 → ℕ),
      I₁.card = 2 → I₂.card = 2 →
      (encodeHat V'' I₁ B).dimcyc ≤ 2 → (encodeHat V'' I₂ B).dimcyc ≤ 2 →
      r₁ ∈ (encodeHat V'' I₁ B).states → r₂ ∈ (encodeHat V'' I₂ B).states →
      (VASS.bridgeUnion (encodeHat V'' I₁ B) (encodeHat V'' I₂ B) r₁ r₂).Reach
        (Sum.inl (p, restrictI I₁ s)) s (Sum.inr (q, restrictI I₂ t)) t →
      ∃ π', (VASS.bridgeUnion (encodeHat V'' I₁ B) (encodeHat V'' I₂ B) r₁ r₂).IsRun
          (Sum.inl (p, restrictI I₁ s)) s π' (Sum.inr (q, restrictI I₂ t)) t ∧
        π'.length ≤ (B + (VASS.bridgeUnion (encodeHat V'' I₁ B) (encodeHat V'' I₂ B) r₁ r₂).size3 s t) ^ c := by sorry

end VAS5Reach
