-- Prove2me | Theorems.Thm_ReplicableOL_lemma_3_2
-- name    : ReplicableOL.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:08.573373+00:00
-- url     : https://prove2.me/theorems/f5f29bd9-ab14-4ae8-819d-566629e3b91a
-- title:
--   Lemma 3.2 — regret identity
-- statement:
--   For every learner satisfying (H2), every seed value and every outcome,
--   $$
--   \mathrm{Reg}_T=|X|-V-\Gamma+N,
--   $$
--   where $X=\sum_j(L\mu_j+Z_j)$, $V=\sum_j(1-2\bar p_j)L\mu_j$, $\Gamma=\sum_j2L\mu_j(\bar p_j-p_j)$ and $N=\sum_{t\le kL}\sigma_t\varepsilon_t$.
--
--   The identity splits the regret into the comparator's advantage, a predictable term, the replicability-sensitive gain and the noise.
--
--   **Formalization Note** The outcome is a block sequence $b$, through `embed`; trailing rounds contribute the same to the learner and to every expert. Lean's $p_j$ comes from the learner's epoch rule at $r$.
--
--   Differences from the source:
--   - encoding: every outcome of Construction C → every block sequence $b$ with the loss sequence `embed T (T / L) L b`, and every $\theta$, $\Delta$; reason: $P_\theta$ is carried by these sequences; the identity is algebraic in $\theta$
--   - encoding: $L\ge1$ implicit in Construction C → `1 ≤ L`; reason: Lean's `T / 0 = 0` is excluded
--   - encoding: a learner whose maps $a_t$ read $[0,1]$-valued losses → `Learner` with maps on all real loss vectors (`Fin t → Fin 2 → ℝ`); reason: a learner on $[0,1]$ extends measurably to $\mathbb R$ and a `Learner` restricts to $[0,1]$; every law and every `embed` sequence here is carried by $[0,1]^2$
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.2, p.12

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_regret
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_embed
import Definitions.Def_ReplicableOL_Learner_toEpochRule
import Definitions.Def_ReplicableOL_gain
import Definitions.Def_ReplicableOL_Vterm
import Definitions.Def_ReplicableOL_Nterm
import Definitions.Def_ReplicableOL_Xterm
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 3.2.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.2, p.12. `Reg_T = |X| − V − Γ + N`.

**Formalization Note.** `S` is the loss sequence `embed` of the bits `b`, and `Φ` is the learner's epoch rule at `r`. The identity holds for every `θ` and every `Δ`, as the page's "every outcome" requires, since `X`, `V + Γ − N` do not depend on `θ`'s being the true mean. -/
theorem lemma_3_2 {T L : ℕ} {R : Type*} [MeasurableSpace R] (hL : 1 ≤ L) (𝓛 : Learner 2 T R) (r : R)
    (Δ : ℝ) (θ : Fin (T / L) → ℝ) (b : Bits (T / L) L) :
    regret 𝓛 (embed T (T / L) L b) r =
      |Xterm θ b| - Vterm Δ (𝓛.toEpochRule L r) θ b - gain Δ (𝓛.toEpochRule L r) θ b +
        Nterm (𝓛.toEpochRule L r) θ b := by sorry

end ReplicableOL
