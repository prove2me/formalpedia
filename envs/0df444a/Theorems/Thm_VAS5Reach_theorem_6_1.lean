-- Prove2me | Theorems.Thm_VAS5Reach_theorem_6_1
-- name    : VAS5Reach.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:31.087109+00:00
-- url     : https://prove2.me/theorems/65fc390b-7a67-4d4d-a190-7cfff7617fac
-- title:
--   Theorem 6.1 (CFZ characterization) — every reachable 5-VAS instance reduces to Case I or Case II with $B \le \mathrm{SIZE}^{O(1)}$
-- statement:
--   There is a constant $c$ such that for every 5-VAS $(V, s, t)$ with $s \xrightarrow{*} t$ there exist $B \le \mathrm{SIZE}(V, s, t)^c$ and a VASS $(V', s', t')$ with $s' \xrightarrow{*} t'$ in $V'$ and
--   $$
--   \ell_V(s, t) \le \ell_{V'}(s', t'),
--   $$
--   such that one of the following holds.
--   1. **Case I.** $V'$ consists of the two disjoint 5-VASS $\widehat{[\![V'']\!]}_{I_1,B}$ and $\widehat{[\![V'']\!]}_{I_2,B}$ connected by a zero-effect transition from the first to the second, where $V''$ is a 5-VASS with $\mathrm{SIZE}(V'') \le \mathrm{SIZE}(V, s, t)^c$, $|I_i| = 2$ and $\dim_{\mathrm{cyc}}(\widehat{[\![V'']\!]}_{I_i,B}) \le 2$ for $i = 1, 2$; the source and target are $s' = (p, s{\restriction}_{I_1})(s)$ and $t' = (q, t{\restriction}_{I_2})(t)$ for states $p, q$ of $V''$.
--   2. **Case II.** $(V', s', t')$ is the $B$-encoding $([\![V]\!]_B, [\![s]\!]_B, [\![t]\!]_B)$.
--
--   This is the paper's reformulation of [CFZ26, Proposition 5.1]; it reduces Theorem 1.2 to Proposition 6.2 (Case I) and Proposition 6.5 (Case II). The proof is in the cited work (the construction is recalled in App. D.1).
--
--   **Formalization Note** $\ell_V(s,t) \le \ell_{V'}(s',t')$ is stated as: every run of $V'$ from $s'$ to $t'$ of length $n$ yields a run of $V$ from $s$ to $t$ of length at most $n$.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ ℓ_{V′}(s′, t′) → every run of V′ from s′ to t′ of length n gives a run of V from s to t of length ≤ n; reason: the two minima compared without forming them; s′ →* t′ is asserted separately
--   - encoding: V′ consists of two disjoint 5-VASS connected by a zero-effect transition from the first to the second → V′ = bridgeUnion of the two retained-coordinate encodings at states r₁, r₂ of the two copies; reason: the disjoint union of the two state sets plus the transition (r₁(u₁), 0, r₂(u₂)) named on p.26
--   - reading: Case II: [[V]]_B, with I the first two coordinates (w.l.o.g., p.16) → [[V]]_{I,B} for some set I of two coordinates; reason: the w.l.o.g. renames coordinates, which changes the instance, so the encoded pair is existential
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.1 and the sentence after it, p.25 (PDF p.27); cited from [CFZ26, Proposition 5.1]

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_cycleSpace
import Definitions.Def_VAS5Reach_VASS_bridgeUnion

namespace VAS5Reach

/-- **Theorem 6.1 (CFZ Characterization [CFZ26, Proposition 5.1]).** For every 5-VAS `(V, s, t)`
with `s −∗→ t`, there exists `B ≤ SIZE(V, s, t)^{O(1)}` and a VASS `(V′, s′, t′)` such that
`s′ −∗→ t′` in `V′` and `ℓ_V(s, t) ≤ ℓ_{V′}(s′, t′)`. Moreover, one of the following alternatives
holds:
I. `V′` consists of two disjoint 5-VASS `[[V″]]^_{I₁,B}`, `[[V″]]^_{I₂,B}`, connected by a
zero-effect transition from the first to the second. Here, `V″` is a 5-VASS of size
`SIZE(V, s, t)^{O(1)}`, and for each `i = 1, 2`, we have `|Iᵢ| = 2` and
`dimcyc([[V″]]^_{Iᵢ,B}) ≤ 2`. The source and target configurations of `V′` are
`s′ = (p, s↾I₁)(s)` and `t′ = (q, t↾I₂)(t)`, where `p` and `q` are two states in `V″`.
II. `(V′, s′, t′)` is a single `B`-encoding VAS `([[V]]_B, [[s]]_B, [[t]]_B)` for some
`B ≤ SIZE(V, s, t)^{O(1)}`.
The constant hidden in the `O(1)` exponent above is independent of the input.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.1 and the sentence after it, printed p. 25 (PDF p. 27). Cited from
[CFZ26, Proposition 5.1]; the proof is not in this paper (the construction is recalled in
App. D.1, printed p. 49).

**Formalization Note** One constant `c` bounds both `B` and `SIZE(V″)` for every instance.
`ℓ_V(s, t) ≤ ℓ_{V′}(s′, t′)` is stated as: every run of `V′` from `s′` to `t′` of length `n`
gives a run of `V` from `s` to `t` of length `≤ n`. In Case I, `V′` is
`bridgeUnion [[V″]]^_{I₁,B} [[V″]]^_{I₂,B} r₁ r₂` for states `r₁`, `r₂` of the two copies, on the
disjoint union of their state types. In Case II the encoded pair `I` is any two coordinates (the
paper fixes the first two w.l.o.g.), and `[[s]]_B = ((), s↾I)(s↾[5]∖I)`; that `s↾I, t↾I ∈ [0,B]^I`
is implied by reachability in `[[V]]_B`. -/
theorem theorem_6_1 :
    ∃ c : ℕ, ∀ (T : Finset (Fin 5 → ℤ)) (s t : Fin 5 → ℕ), VASReach T s t →
      ∃ B : ℕ, B ≤ vasSize T s t ^ c ∧
      ((∃ (Q : Type) (V'' : VASS Q (Fin 5)) (I₁ I₂ : Finset (Fin 5)) (p q : Q)
          (r₁ : Q × (I₁ → ℕ)) (r₂ : Q × (I₂ → ℕ)),
          I₁.card = 2 ∧ I₂.card = 2 ∧ V''.size ≤ vasSize T s t ^ c ∧
          (encodeHat V'' I₁ B).dimcyc ≤ 2 ∧ (encodeHat V'' I₂ B).dimcyc ≤ 2 ∧
          p ∈ V''.states ∧ q ∈ V''.states ∧
          r₁ ∈ (encodeHat V'' I₁ B).states ∧ r₂ ∈ (encodeHat V'' I₂ B).states ∧
          (VASS.bridgeUnion (encodeHat V'' I₁ B) (encodeHat V'' I₂ B) r₁ r₂).Reach
            (Sum.inl (p, restrictI I₁ s)) s (Sum.inr (q, restrictI I₂ t)) t ∧
          ∀ π', (VASS.bridgeUnion (encodeHat V'' I₁ B) (encodeHat V'' I₂ B) r₁ r₂).IsRun
              (Sum.inl (p, restrictI I₁ s)) s π' (Sum.inr (q, restrictI I₂ t)) t →
            ∃ ρ, IsVASRun T s ρ t ∧ ρ.length ≤ π'.length) ∨
       (∃ I : Finset (Fin 5), I.card = 2 ∧
          (encode (VASS.ofVAS T) I B).Reach ((), restrictI I s) (restrictC I s)
            ((), restrictI I t) (restrictC I t) ∧
          ∀ π', (encode (VASS.ofVAS T) I B).IsRun ((), restrictI I s) (restrictC I s) π'
              ((), restrictI I t) (restrictC I t) →
            ∃ ρ, IsVASRun T s ρ t ∧ ρ.length ≤ π'.length)) := by sorry

end VAS5Reach
