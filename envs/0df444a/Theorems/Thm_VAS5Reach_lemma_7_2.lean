-- Prove2me | Theorems.Thm_VAS5Reach_lemma_7_2
-- name    : VAS5Reach.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:48.94914+00:00
-- url     : https://prove2.me/theorems/fda8dcd5-cbac-4df4-b3c1-be75112ec272
-- title:
--   Lemma 7.2 — a maximal bounded-coordinate prefix of a run from a non-coverable source
-- statement:
--   There is a constant $c$ such that the following holds. Let $U = (U_1)u_1(U_2)\cdots u_{k-1}(U_k)$ be a sequential 3-VASS and $C \in \mathbb N$. There is $D \le (C + \mathrm{SIZE}(U))^c$ such that for every run $p(x) \xrightarrow{\pi} q(y)$ with $p$ in $U_1$ and $q$ in $U_k$ whose source is not forward $C$-coverable in $U$, there are a coordinate $i$ and a prefix $p(x) \xrightarrow{\pi_0} r(z)$ of $\pi$ with $i \in \mathrm{BD}(\pi_0, D)$ satisfying one of the following:
--   1. $r(z) = q(y)$;
--   2. $r(z)$ is the entry configuration of a later component $U_h$ (the last transition of $\pi_0$ is the bridge into $U_h$), and every $w \in \mathbb N^3$ with
--   $$
--   w(i) \ge z(i), \qquad w(j) \ge D \ \text{ for all } j \ne i
--   $$
--   has $r(w)$ forward $C$-coverable in $U_h$.
--
--   Moreover, $\pi_0$ is captured by a 2-VASS of size at most $D\,\mathrm{SIZE}(U)$: it lifts to a run of the same length of $[\![U]\!]_{\{i\},D-1}$ between the encoded endpoints, and $\mathrm{SIZE}([\![U]\!]_{\{i\},D-1}) \le D\,\mathrm{SIZE}(U)$.
--
--   Differences from the source:
--   - generalization: fix a run …; then there exists an integer D ≤ (C + SIZE(U))^{O(1)} → D chosen before the run, uniformly for all runs of U; reason: ∃D ∀run implies the printed ∀run ∃D, so the printed statement is an instance; App. E.1 defines D from |Q|, ‖T‖, C, SIZE(U) only, and p.32 uses this uniformity
--   - reading: π₀ is captured by a 2-VASS of size at most D SIZE(U) → π₀ lifts to a run of the same length of [[U]]_{{i},D−1}, and SIZE([[U]]_{{i},D−1}) ≤ D·SIZE(U); reason: the meaning fixed in the proof, App. E.1 (p.52)
--   - reading: a sequential sub-VASS (U, p(x), q(y)) considered together with its run → IsSequential U p q: p lies in the first and q in the last component of U; reason: the paper's convention for a sequential VASS with a designated run (p.16: its source and target states belong to U1 and Uk)
--   - encoding: exponent O(1), whose hidden constant is independent of the input (p.25) → one natural-number constant c quantified before every instance; reason: this is the paper's quantifier order; a natural exponent loses nothing because every base is at least 1
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 7.2, p.31 (PDF p.33); proof App. E.1, p.52 (PDF p.54); uniformity p.32 (PDF p.34)

import Mathlib
import Definitions.Def_VAS5Reach_VASS_IsRun
import Definitions.Def_VAS5Reach_encode
import Definitions.Def_VAS5Reach_VASS_IsSeqDecomp
import Definitions.Def_VAS5Reach_VASS_FwdCoverable

namespace VAS5Reach

/-- **Lemma 7.2.** Let `U = (U₁)u₁(U₂) ⋯ u_{k−1}(U_k)` be a sequential 3-VASS, and fix a run
`p(x) −π→ q(y)` whose source is not forward `C`-coverable. Then there exists an integer
`D ≤ (C + SIZE(U))^{O(1)}` such that one can find a coordinate `i ∈ [3]` and a prefix
`p(x) −π₀→ r(z)` with `i ∈ BD(π₀, D)` satisfying one of the following:
1. `r(z) = q(y)`;
2. `r(z)` is the entry configuration of a later component `U_h`, and every `w ∈ ℕ³` satisfying
`w(i) ≥ z(i)`, `w(j) ≥ D` for all `j ≠ i` has `r(w)` forward `C`-coverable in `U_h`.
Moreover, `π₀` is captured by a 2-VASS of size at most `D·SIZE(U)`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), Lemma 7.2, printed p. 31 (PDF p. 33); its proof, App. E.1, printed p. 52
(PDF p. 54), which fixes "captured" and shows that `D` depends only on `|Q|`, `∥T∥`, `C` and
`SIZE(U)`; uniformity used on printed p. 32 (PDF p. 34): "the threshold in Lemma 7.2 can be
chosen uniformly over all sequential subinstances".

**Formalization Note** `D` is chosen before the run (uniform over all runs of `U`), the stronger
reading, which App. E.1 proves and p. 32 uses. The run starts in the first and ends in the last
component (the paper's convention for a sequential VASS with a designated run, printed p. 16); the
components are `Cs 0, …, Cs k` and the bridges `bs 0, …, bs (k−1)`. "Prefix" means `π = π₀ π₁`.
"Entry configuration of a later component `U_h`" means that the last transition of `π₀` is the
bridge into that component (`bs h`, entering `Cs (h+1)`); forward `C`-coverability is in that
component alone. "Captured by a 2-VASS of size at most `D·SIZE(U)`" is, as in App. E.1: `π₀` lifts
to a run of the same length of `[[U]]_{{i},D−1}` (coordinate `i` encoded in `{0, …, D − 1}`)
between the encoded endpoints, and `SIZE([[U]]_{{i},D−1}) ≤ D·SIZE(U)`. `O(1)` is one constant
`c` quantified first. -/
theorem lemma_7_2 :
    ∃ c : ℕ, ∀ {ι Q : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι = 3 →
      ∀ (U : VASS Q ι) (k : ℕ) (Cs : Fin (k + 1) → VASS Q ι) (bs : Fin k → Q × (ι → ℤ) × Q),
      U.IsSeqDecomp k Cs bs → ∀ C : ℕ, ∃ D : ℕ, D ≤ (C + U.size) ^ c ∧
      ∀ (p q : Q) (x y : ι → ℕ) (π : List (Q × (ι → ℤ) × Q)),
        p ∈ (Cs 0).states → q ∈ (Cs (Fin.last k)).states →
        U.IsRun p x π q y → ¬ U.FwdCoverable C p x →
        ∃ (i : ι) (π₀ π₁ : List (Q × (ι → ℤ) × Q)) (r : Q) (z : ι → ℕ),
          π = π₀ ++ π₁ ∧ U.IsRun p x π₀ r z ∧ i ∈ VASS.BD x π₀ D ∧
          ((r = q ∧ z = y) ∨
            ∃ h : Fin k, π₀.getLast? = some (bs h) ∧
              ∀ w : ι → ℕ, z i ≤ w i → (∀ j, j ≠ i → D ≤ w j) →
                (Cs h.succ).FwdCoverable C r w) ∧
          (∃ π₀' : List ((Q × (({i} : Finset ι) → ℕ)) × ({j // j ∉ ({i} : Finset ι)} → ℤ) ×
              (Q × (({i} : Finset ι) → ℕ))),
            (encode U {i} (D - 1)).IsRun (p, restrictI {i} x) (restrictC {i} x) π₀'
              (r, restrictI {i} z) (restrictC {i} z) ∧ π₀'.length = π₀.length) ∧
          (encode U {i} (D - 1)).size ≤ D * U.size := by sorry

end VAS5Reach
