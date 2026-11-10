-- Prove2me | Theorems.Thm_VAS5Reach_theorem_6_3
-- name    : VAS5Reach.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:32.76102+00:00
-- url     : https://prove2.me/theorems/8941451c-51de-4974-af04-68be5c835958
-- title:
--   Theorem 6.3 (efficient hybrid-set representations) — $\mathrm{Reach}^q_V(p(H))$ is a finite union of hybrid sets of norm $\mathrm{poly}(\mathrm{SIZE}(V)+\mathrm{NORM}(H))$
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a 3-VASS with $\dim_{\mathrm{cyc}}(V) \le 2$, and let $H = b + P^{\langle c,\cdot\rangle \le K}$ be a hybrid set whose periods satisfy $P \subseteq \mathrm{CYC}(V)$. For any states $p, q$ of $V$, the set
--   $$
--   \mathrm{Reach}^q_V(p(H)) = \{\, y : p(x) \xrightarrow{*} q(y) \text{ for some } x \in H \,\}
--   $$
--   is a finite union of hybrid sets $H'$ with $\mathrm{NORM}(H') \le (\mathrm{SIZE}(V) + \mathrm{NORM}(H))^c$.
--
--   This is [CFF+26, Theorem 4.2], used in the proof of Proposition 6.2; the proof is in the cited work.
--
--   Differences from the source:
--   - encoding: poly(SIZE(V) + NORM(H)), one polynomial for all inputs → (SIZE(V) + NORM(H))^c with one constant c quantified first; reason: a polynomial is bounded by a power of its argument, which is at least 2
--   - encoding: a finite union of hybrid sets H′ → a list of hybrid-set representations whose members are exactly the reachable vectors; reason: a finite union given by its members
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.3, p.25 (PDF p.27); cited from [CFF+26, Theorem 4.2]

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_VASS_cycleSpace
import Definitions.Def_VAS5Reach_HybridSet

namespace VAS5Reach

/-- **Theorem 6.3 (Efficient Hybrid-Set Representations [CFF+26, Theorem 4.2]).** Let `V` be a
3-VASS with `dimcyc(V) ≤ 2`. Let `H = b + P^{⟨c,·⟩≤K}` be a hybrid set whose periods satisfy
`P ⊆ CYC(V)`. For any states `p`, `q`, the set `Reach^q_V(p(H))` is a finite union of hybrid
sets `H′` satisfying `NORM(H′) ≤ poly(SIZE(V) + NORM(H))`.

Here `Reach^q_V(p(X)) := ⋃_{x∈X} Reach^q_V(p(x))` is the set of vectors reachable at `q` from some
configuration `p(x)` with `x ∈ X`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Theorem 6.3, printed p. 25 (PDF p. 27), and the definition of `Reach^q_V(p(X))` just
before it. Cited from [CFF+26, Theorem 4.2]; the proof is not in this paper.

**Formalization Note** "poly" is one polynomial for all `V`, `H`, `p`, `q`, written
`(SIZE(V) + NORM(H))^c` with `c` quantified first. The finite union is a list `L` of hybrid-set
representations whose members are exactly the vectors `y` with `p(x) −∗→ q(y)` for some
`x ∈ H`. A 3-VASS is a VASS whose coordinate type has three elements; `P ⊆ CYC(V)` casts each
period to `ℚ^3`. -/
theorem theorem_6_3 :
    ∃ c : ℕ, ∀ {ι Q : Type} [Fintype ι] (V : VASS Q ι), Fintype.card ι = 3 → V.dimcyc ≤ 2 →
      ∀ H : HybridSet ι, (∀ i, (fun j => ((H.per i j : ℕ) : ℚ)) ∈ V.cycleSpace) →
      ∀ p ∈ V.states, ∀ q ∈ V.states,
      ∃ L : List (HybridSet ι), (∀ H' ∈ L, H'.norm ≤ (V.size + H.norm) ^ c) ∧
        ∀ y : ι → ℕ, (∃ x, H.Mem x ∧ V.Reach p x q y) ↔ ∃ H' ∈ L, H'.Mem y := by sorry

end VAS5Reach
