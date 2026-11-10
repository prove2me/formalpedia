-- Prove2me | Theorems.Thm_VAS5Reach_corollary_4_6
-- name    : VAS5Reach.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:15.711193+00:00
-- url     : https://prove2.me/theorems/3b5f0055-21ae-4f2d-8a44-71595c71a1b3
-- title:
--   Corollary 4.6 — a path of $[\![V]\!]_B$ splits into short $\alpha$, $\beta$ and simple cycles relocatable in $[\![V]\!]_{2B}$
-- statement:
--   Let $V$ be a $(d+2)$-VAS with transition set $T$, $I$ a set of two coordinates, $B \in \mathbb N$, and let $\pi$ be a path in $[\![V]\!]_{I,B}$ from $p$ to $q$. There is a path $\alpha\gamma_1\cdots\gamma_n\beta$ from $p$ to $q$ in $[\![V]\!]_{I,2B}$ such that:
--   1. the prefix $\alpha$ and the suffix $\beta$ are paths in $[\![V]\!]_{I,B}$ with $|\alpha|, |\beta| \le (B+1)^2 - 1$;
--   2. each $\gamma_i$ is a simple cycle in $[\![V]\!]_{I,2B}$ of length at most $(B+1)^2$;
--   3. $\psi_\pi = \psi_\alpha + \sum_{i=1}^n \psi_{\gamma_i} + \psi_\beta$, Parikh images counting underlying transitions of $T$.
--
--   Consequently $\alpha\gamma_{\sigma(1)}\cdots\gamma_{\sigma(n)}\beta$ is a path in $[\![V]\!]_{I,2B}$ for every permutation $\sigma$.
--
--   Differences from the source:
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: Parikh vectors ψ ∈ ℕ^m and cycles γ₁, …, γₙ → count functions of the underlying transition sequences; the cycles as a list, permuted through their indices; reason: same data without an enumeration of T
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 4.6, pp.18–19 (PDF pp.20–21); standing assumptions of §4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_cycleSpace

namespace VAS5Reach

/-- **Corollary 4.6.** Let `π` be a path in `[[V]]_B` from `p` to `q`. There exists a path
`αγ₁ ⋯ γₙβ` from `p` to `q` in `[[V]]_{2B}` such that:
1. The prefix `α` and the suffix `β` are paths in `[[V]]_B`, with `|α|, |β| ≤ (B + 1)² − 1`.
2. Each `γᵢ` is a simple cycle in `[[V]]_{2B}` of length at most `(B + 1)²`.
3. `ψ_π = ψ_α + Σᵢ ψ_{γᵢ} + ψ_β`.
Consequently `αγ_{σ(1)} ⋯ γ_{σ(n)}β` is a path in `[[V]]_{2B}` for every permutation `σ`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 4.6, printed pp. 18–19 (PDF pp. 20–21); §4 standing assumptions, printed
p. 17 (PDF p. 19): `V` is a `(d + 2)`-VAS with transition set `T`, and "Parikh images of paths in
[[V]]_B count their underlying transitions in T".

**Formalization Note** `p`, `q` are states of `[[V]]_{I,B}` for any pair `I` of coordinates
(the paper fixes the first two w.l.o.g.). `[[V]]_B` and `[[V]]_{2B}` share the state type, and
every transition of `[[V]]_B` is one of `[[V]]_{2B}`. Parikh images are of the sequences of
underlying VAS transitions. The cycles are a list `γ`; a permutation acts on their indices. -/
theorem corollary_4_6 {ι : Type} [Fintype ι] (T : Finset (ι → ℤ)) (I : Finset ι) (B : ℕ)
    (hI : I.card = 2) (p q : Unit × (I → ℕ))
    (π : List ((Unit × (I → ℕ)) × ({i // i ∉ I} → ℤ) × (Unit × (I → ℕ))))
    (hπ : (encode (VASS.ofVAS T) I B).IsPath p π q) :
    ∃ (α : List ((Unit × (I → ℕ)) × ({i // i ∉ I} → ℤ) × (Unit × (I → ℕ))))
      (γ : List (List ((Unit × (I → ℕ)) × ({i // i ∉ I} → ℤ) × (Unit × (I → ℕ)))))
      (β : List ((Unit × (I → ℕ)) × ({i // i ∉ I} → ℤ) × (Unit × (I → ℕ)))),
      (encode (VASS.ofVAS T) I (2 * B)).IsPath p (α ++ γ.flatten ++ β) q ∧
      (∃ r, (encode (VASS.ofVAS T) I B).IsPath p α r) ∧
      (∃ r, (encode (VASS.ofVAS T) I B).IsPath r β q) ∧
      α.length ≤ (B + 1) ^ 2 - 1 ∧ β.length ≤ (B + 1) ^ 2 - 1 ∧
      (∀ g ∈ γ, (encode (VASS.ofVAS T) I (2 * B)).IsSimpleCycle g ∧ g.length ≤ (B + 1) ^ 2) ∧
      parikh (π.map (underlying I)) = parikh (α.map (underlying I)) +
        (γ.map fun g => parikh (g.map (underlying I))).sum + parikh (β.map (underlying I)) ∧
      ∀ σ : Equiv.Perm (Fin γ.length),
        (encode (VASS.ofVAS T) I (2 * B)).IsPath p
          (α ++ (List.ofFn fun i => γ.get (σ i)).flatten ++ β) q := by sorry

end VAS5Reach
