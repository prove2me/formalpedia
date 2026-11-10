-- Prove2me | Theorems.Thm_VAS5Reach_lemma_6_17
-- name    : VAS5Reach.lemma_6_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:00.18896+00:00
-- url     : https://prove2.me/theorems/e1c716a2-afbe-4652-8cfa-0fa7d30d6457
-- title:
--   Lemma 6.17 — coverable hybrid endpoints admit short members and a short run between them
-- statement:
--   There is a constant $c$ such that the following holds. Let $V$ be a 5-VAS with transition set $T$, $I$ a set of two coordinates, $B \in \mathbb N$, $C$ a transformation-area threshold for $[\![V]\!]_{I,B}$, and $H_1$, $H_2$ hybrid sets at states $p$, $q$ of a sequential sub-VASS $U$ of $[\![V]\!]_{I,B}$, with $p$ in the first and $q$ in the last component. Suppose that $p(x) \xrightarrow{*} q(y)$ in $U$ for some $x \in H_1$, $y \in H_2$, that $H_1$ is forward $C$-coverable in $U$ and that $H_2$ is backward $C$-coverable in $U$. Then there exist $x' \in H_1$ and $y' \in H_2$ such that
--   $$
--   \|x'\|,\ \|y'\|,\ \ell_V\bigl((p, x'), (q, y')\bigr) \le \bigl(B + C + \mathrm{SIZE}(V) + \mathrm{NORM}(H_1) + \mathrm{NORM}(H_2)\bigr)^c .
--   $$
--   The bound does not depend on $x$ or $y$.
--
--   Differences from the source:
--   - encoding: ℓ_V(s, t) ≤ N, with ℓ_V(s, t) := min LEN(V, s, t) (∞ if t is unreachable) → some run of V from s to t has length ≤ N; reason: for a reachable target the two are equivalent; no minimum (and no junk value of an empty infimum) is formed
--   - reading: a sequential sub-VASS (U, p(x), q(y)) considered together with its run → IsSequential U p q: p lies in the first and q in the last component of U; reason: the paper's convention for a sequential VASS with a designated run (p.16: its source and target states belong to U1 and Uk)
--   - generalization: [[V]]_B with I the first two coordinates (assumed w.l.o.g., p.16) → [[V]]_{I,B} for every set I of two coordinates; reason: renaming coordinates maps any pair to the first two, so the paper's case I = {1, 2} is an instance
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.17, p.30 (PDF p.32); Definition 6.15, p.30

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun
import Definitions.Def_VAS5Reach_vasSize
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_IsSeqDecomp
import Definitions.Def_VAS5Reach_VASS_FwdCoverable
import Definitions.Def_VAS5Reach_IsTAThreshold
import Definitions.Def_VAS5Reach_HybridSet

namespace VAS5Reach

/-- **Lemma 6.17.** Let `V` be a 5-VAS, `B ∈ ℕ`, and `C` a transformation-area threshold for
`[[V]]_B`. Let `H₁`, `H₂` be hybrid sets at states `p`, `q` of a sequential sub-VASS `U` of
`[[V]]_B`. Suppose that there exist `x ∈ H₁` and `y ∈ H₂` such that `p(x) −∗→ q(y)` in `U`. Assume
that `H₁` is forward `C`-coverable in `U` and `H₂` is backward `C`-coverable in `U`. Then there
exist `x′ ∈ H₁` and `y′ ∈ H₂` such that
`∥x′∥, ∥y′∥, ℓ_V((p, x′), (q, y′)) ≤ (B + C + SIZE(V) + NORM(H₁) + NORM(H₂))^{O(1)}`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 6.17, printed p. 30 (PDF p. 32); coverability of hybrid sets: Definition 6.15,
printed p. 30 (PDF p. 32).

**Formalization Note** The hybrid sets live in `ℕ^{[5]∖I}` (the counters of `U`). The bound has no
`∥x∥`, `∥y∥` term. `SIZE(V)` is the size of the 5-VAS (`vasSizeV`). The sequential sub-VASS `U` comes with its designated run from `p` to `q`, so by the paper's convention
(printed p. 16) its source state `p` lies in its first and its target state `q` in its last
component (`IsSequential U p q`). The encoded pair `I` is any two coordinates (the paper fixes the
first two w.l.o.g.); `s = (p, x)` and `t = (q, y)` restore the encoded values (`decode`).
`ℓ_V(s, t) ≤ N` is stated as a run of `V` of length `≤ N`; `O(1)` is one constant `c` quantified
before every instance. `C` is any transformation-area threshold for `[[V]]_B` (a hypothesis). -/
theorem lemma_6_17 :
    ∃ c : ℕ, ∀ (T : Finset (Fin 5 → ℤ)) (I : Finset (Fin 5)) (B C : ℕ), I.card = 2 →
      IsTAThreshold T I B C →
      ∀ (U : VASS (Unit × (I → ℕ)) {i // i ∉ I}) (p q : Unit × (I → ℕ))
        (H₁ H₂ : HybridSet {i // i ∉ I}),
      U.IsSubVASS (encode (VASS.ofVAS T) I B) → U.IsSequential p q →
      (∃ x y, H₁.Mem x ∧ H₂.Mem y ∧ U.Reach p x q y) →
      U.HybFwdCoverable C p H₁ → U.HybBwdCoverable C q H₂ →
      ∃ x' y', H₁.Mem x' ∧ H₂.Mem y' ∧
        supNormN x' ≤ (B + C + vasSizeV T + H₁.norm + H₂.norm) ^ c ∧
        supNormN y' ≤ (B + C + vasSizeV T + H₁.norm + H₂.norm) ^ c ∧
        ∃ ρ, IsVASRun T (decode I p.2 x') ρ (decode I q.2 y') ∧
          ρ.length ≤ (B + C + vasSizeV T + H₁.norm + H₂.norm) ^ c := by sorry

end VAS5Reach
