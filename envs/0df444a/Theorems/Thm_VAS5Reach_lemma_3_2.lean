-- Prove2me | Theorems.Thm_VAS5Reach_lemma_3_2
-- name    : VAS5Reach.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:31.854306+00:00
-- url     : https://prove2.me/theorems/eca319dc-5e90-443b-adaf-5d539a21fc95
-- title:
--   Lemma 3.2 — if every coordinate exceeds $D_0 = (C + \mathrm{SIZE}(V))^{O((d+1)!)}$ along a run, a short run reaches $\ge C\cdot\mathbf 1$
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a $d$-VASS, $s = p(x)$ a configuration and $C \in \mathbb N$, and set
--   $$
--   D_0 := (C + \mathrm{SIZE}(V))^{c\,(d+1)!}.
--   $$
--   If every coordinate reaches a value at least $D_0$ somewhere along a run $\pi$ from $s$ in $V$, i.e. $\mathrm{BD}(\pi, D_0) = \emptyset$, then there is a run $\rho$ from $s$ with $|\rho| \le D_0$ ending at a configuration $q(z)$ with $z \ge C \cdot \mathbf 1$. Moreover, $\rho$ is obtained by deleting cycles from $\pi$ and has the same final state $q$ as $\pi$. This is [CFZ26, Lemma 3.3]; the proof is in the cited work.
--
--   Differences from the source:
--   - encoding: D₀ := (C + SIZE(V))^{O((d+1)!)} → D₀ = (C + SIZE(V))^{c·(d+1)!} with one constant c quantified before every instance; reason: O((d+1)!) ≤ c·(d+1)! for a suitable c; the threshold is the printed expression
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 3.2, p.16 (PDF p.18); cited from [CFZ26, Lemma 3.3]

import Mathlib
import Definitions.Def_VAS5Reach_VASS
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_VASS_FwdCoverable
import Definitions.Def_VAS5Reach_VASS_DeletesCycles

namespace VAS5Reach

/-- **Lemma 3.2 ([CFZ26, Lemma 3.3]).** For every `d`-VASS `(V, s)` and number `C ∈ ℕ`, there exists
a threshold `D₀ := (C + SIZE(V))^{O((d+1)!)}` such that, if every coordinate reaches a value at least
`D₀` somewhere along a run `π` from `s` in `V`, i.e., `BD(π, D₀) = ∅`, there is also a run `ρ` from
`s` with `|ρ| ≤ D₀` and ending at `q(x)` satisfying `x ≥ C·1`. Moreover, `ρ` is obtained by deleting
cycles from `π` and therefore has the same final state as `π`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 3.2, printed p. 16 (PDF p. 18). Cited from [CFZ26, Lemma 3.3]; the proof is
not in this paper.

**Formalization Note** `d = Fintype.card ι`; `D₀` is exactly `(C + SIZE(V))^{c·(d+1)!}` with one `c`
quantified before every instance. `s = p(x)`; the run `π` ends at `q(y)`, and `ρ` ends at the same
state `q` with counters `z ≥ C·1`. "Obtained by deleting cycles" is `DeletesCycles` (successive
removals of cycle segments). -/
theorem lemma_3_2 :
    ∃ c : ℕ, ∀ {ι Q : Type} [Fintype ι] (V : VASS Q ι) (p : Q) (x : ι → ℕ) (C : ℕ)
      (π : List (Q × (ι → ℤ) × Q)) (q : Q) (y : ι → ℕ),
      V.IsRun p x π q y →
      VASS.BD x π ((C + V.size) ^ (c * (Fintype.card ι + 1).factorial)) = ∅ →
      ∃ (ρ : List (Q × (ι → ℤ) × Q)) (z : ι → ℕ), V.IsRun p x ρ q z ∧
        ρ.length ≤ (C + V.size) ^ (c * (Fintype.card ι + 1).factorial) ∧
        (∀ i, C ≤ z i) ∧ V.DeletesCycles π ρ := by sorry

end VAS5Reach
