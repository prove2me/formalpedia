-- Prove2me | Theorems.Thm_ReplicableOL_lemma_3_4
-- name    : ReplicableOL.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:53:44.79319+00:00
-- url     : https://prove2.me/theorems/498a4169-c6f0-403a-88bd-362f7eb53604
-- title:
--   Lemma 3.4 — the learner's terms
-- statement:
--   (a) $\mathbb EV=0$, $\mathbb EV^2\le s_\mu^2$ and $\mathbb EV^4\le3s_\mu^4$.
--
--   (b) $\mathbb EN=0$, $\mathbb EN^2\le kL/4$, and $\mathbb EN^4\le0.205(kL)^2$ when $kL\ge100$.
--
--   (c) Hence $\widetilde W:=|X|-V+N=\mathrm{Reg}_T+\Gamma$ satisfies $\mathbb E\widetilde W=A$ and
--   $$
--   \|\widetilde W\|_4\le3^{1/4}(s+s_\mu)+0.673\sqrt{kL},
--   $$
--   which is at most $1.5265\,\varsigma$ in the regime $k\ge100$, $\Delta\sqrt L\ge100$, with $\varsigma=\Delta L\sqrt k$.
--
--   All expectations are over $(\theta,S)$ at a fixed seed. This is the one place where within-epoch causality is used: a learner that reads the current bit has a much larger $N$.
--
--   **Formalization Note** The rule $\Phi$ is any round-causal epoch rule; a learner's rule at a seed is one.
--
--   Differences from the source:
--   - generalization: every learner satisfying (H2), at a fixed seed → every round-causal epoch rule `Φ` ((a) needs no causality), with a conjunct that a learner's rule is round-causal; reason: the page's learners are the case $\Phi=$ `𝓛.toEpochRule L r`; the proof uses only causality
--   - reading: (c) "Hence" $\|\widetilde W\|_4\le3^{1/4}(s+s_\mu)+0.673\sqrt{kL}$, with no condition on $kL$ → the same bound with `100 ≤ k * L`; reason: (c) is derived from (b), whose fourth moment bound has this condition
--   - encoding: $\|\widetilde W\|_4$ → `(E1 W̃⁴)^(1/4)`; reason: the definition of the norm
--   - encoding: $s$, $s_\mu$ → `√(sSq k L Δ)`, `√(sMuSq k L Δ)` in `wBound`; reason: the definitions on p.10
--   - encoding: a learner whose maps $a_t$ read $[0,1]$-valued losses → `Learner` with maps on all real loss vectors (`Fin t → Fin 2 → ℝ`); reason: a learner on $[0,1]$ extends measurably to $\mathbb R$ and a `Learner` restricts to $[0,1]$; every law and every `embed` sequence here is carried by $[0,1]^2$
--   - encoding: $L\ge1$ implicit in Construction C (an epoch length) → `1 ≤ L`; reason: an epoch of length $0$ has no fraction $p_j$; Lean's `/ 0 = 0` is excluded
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.4, p.12

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_regret
import Definitions.Def_ReplicableOL_Bits
import Definitions.Def_ReplicableOL_embed
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_IsRoundCausal
import Definitions.Def_ReplicableOL_Learner_toEpochRule
import Definitions.Def_ReplicableOL_E1
import Definitions.Def_ReplicableOL_gain
import Definitions.Def_ReplicableOL_Vterm
import Definitions.Def_ReplicableOL_Nterm
import Definitions.Def_ReplicableOL_Xterm
import Definitions.Def_ReplicableOL_Wtilde
import Definitions.Def_ReplicableOL_sMuSq
import Definitions.Def_ReplicableOL_wBound
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Lemma 3.4.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.4, p.12. All clauses. (a) holds for any rule; (b) and (c) use `IsRoundCausal`, which every learner's rule has (last conjuncts).

**Formalization Note.** `(E1 Y⁴)^{1/4}` is `‖Y‖₄`. `F_j` and `H_t` of the page are used only in the proof. The norm bound carries `100 ≤ kL`, since (c) is "Hence" from (b), whose fourth moment bound requires it. -/
theorem lemma_3_4 {k L : ℕ} {Δ : ℝ} {R : Type*} [MeasurableSpace R] (hL : 1 ≤ L)
    (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (Φ : EpochRule k L) :
    -- (a)
    E1 Δ (fun θ S => Vterm Δ Φ θ S) = 0 ∧
    E1 Δ (fun θ S => Vterm Δ Φ θ S ^ 2) ≤ sMuSq k L Δ ∧
    E1 Δ (fun θ S => Vterm Δ Φ θ S ^ 4) ≤ 3 * sMuSq k L Δ ^ 2 ∧
    (IsRoundCausal Φ →
      -- (b)
      E1 Δ (fun θ S => Nterm Φ θ S) = 0 ∧
      E1 Δ (fun θ S => Nterm Φ θ S ^ 2) ≤ (k : ℝ) * L / 4 ∧
      (100 ≤ k * L → E1 Δ (fun θ S => Nterm Φ θ S ^ 4) ≤ 0.205 * ((k : ℝ) * L) ^ 2) ∧
      -- (c)
      E1 Δ (fun θ S => Wtilde Δ Φ θ S) = E1 Δ (fun θ (S : Bits k L) => |Xterm θ S|) ∧
      (100 ≤ k * L → (E1 Δ (fun θ S => Wtilde Δ Φ θ S ^ 4)) ^ (1 / 4 : ℝ) ≤ wBound k L Δ) ∧
      (100 ≤ k → 100 ≤ Δ * √(L : ℝ) →
        wBound k L Δ ≤ 1.5265 * (Δ * L * √(k : ℝ)))) ∧
    -- `W̃ = Reg_T + Γ`, and a learner's rule is round-causal
    (∀ (T : ℕ) (𝓛 : Learner 2 T R) (r : R), IsRoundCausal (𝓛.toEpochRule L r) ∧
      ∀ (θ : Fin (T / L) → ℝ) (b : Bits (T / L) L),
        Wtilde Δ (𝓛.toEpochRule L r) θ b =
          regret 𝓛 (embed T (T / L) L b) r + gain Δ (𝓛.toEpochRule L r) θ b) := by sorry

end ReplicableOL
