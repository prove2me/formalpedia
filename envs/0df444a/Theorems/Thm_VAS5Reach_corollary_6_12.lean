-- Prove2me | Theorems.Thm_VAS5Reach_corollary_6_12
-- name    : VAS5Reach.corollary_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:10.027204+00:00
-- url     : https://prove2.me/theorems/cfebe1e4-cb78-4309-a87d-01074c3bfa93
-- title:
--   Corollary 6.12 — $\mathbb Z$-runs between points of $\mathcal G_C$ give runs of length $(\mathrm{SIZE}(U) + \|x\| + \|y\|)^{\mathrm{poly}(d)}$
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a $(d+2)$-VAS with transition set $T$, $I$ a set of two coordinates, $B \in \mathbb N$, $U$ a sub-VASS of $[\![V]\!]_{I,B}$ and $C$ a transformation-area threshold for $[\![V]\!]_{I,B}$. If $p(x) \xrightarrow{*}_{\mathbb Z} q(y)$ in $U$ and $x, y \ge C \cdot \mathbf 1$, then
--   $$
--   \ell_V\bigl((p, x), (q, y)\bigr) \le \bigl(\mathrm{SIZE}(U) + \|x\| + \|y\|\bigr)^{c(d+1)^c}.
--   $$
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: exponent poly(d) → c·(d + 1)^c with one constant c quantified before d and every instance; reason: every polynomial in d is bounded by c(d + 1)^c for a suitable c
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 6.12, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_VAS5Reach_supNorm
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_IsSeqDecomp
import Definitions.Def_VAS5Reach_IsTAThreshold

namespace VAS5Reach

/-- **Corollary 6.12.** Let `V` be a `(d + 2)`-VAS, `B ∈ ℕ`, and `U` a sub-VASS of `[[V]]_B`. Let `C`
be a transformation-area threshold for `[[V]]_B`. If `p(x) −∗→_Z q(y)` in `U` and `x, y ≥ C·1`,
then `ℓ_V((p, x), (q, y)) ≤ (SIZE(U) + ∥x∥ + ∥y∥)^{poly(d)}`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Corollary 6.12, printed p. 28 (PDF p. 30).

**Formalization Note** `d + 2 = Fintype.card ι`; `poly(d)` is `c(d + 1)^c` with one `c` quantified
before `d` and every instance. `U` is any sub-VASS (not necessarily sequential). `x`, `y` are the
counter vectors of `U` (coordinates outside `I`), and `(p, x)`, `(q, y)` restore the encoded values
(`decode`). The encoded pair `I` is any two coordinates. -/
theorem corollary_6_12 :
    ∃ c : ℕ, ∀ (d : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι = d + 2 →
      ∀ (T : Finset (ι → ℤ)) (I : Finset ι) (B C : ℕ), I.card = 2 → IsTAThreshold T I B C →
      ∀ (U : VASS (Unit × (I → ℕ)) {i // i ∉ I}), U.IsSubVASS (encode (VASS.ofVAS T) I B) →
      ∀ (p q : Unit × (I → ℕ)) (x y : {i // i ∉ I} → ℕ),
      U.ZReach p (fun j => (x j : ℤ)) q (fun j => (y j : ℤ)) →
      (∀ j, C ≤ x j) → (∀ j, C ≤ y j) →
      ∃ ρ, IsVASRun T (decode I p.2 x) ρ (decode I q.2 y) ∧
        ρ.length ≤ (U.size + supNormN x + supNormN y) ^ (c * (d + 1) ^ c) := by sorry

end VAS5Reach
