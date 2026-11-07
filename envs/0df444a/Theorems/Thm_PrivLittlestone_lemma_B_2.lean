-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_B_2
-- name    : PrivLittlestone.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:36:49.556693+00:00
-- url     : https://prove2.me/theorems/1d93f78e-c350-4a4f-8177-3fa020d2f5c7
-- title:
--   Lemma B.2 — endpoint ratios $e^{-s\chi} \le p_0/p_1 \le e^{s\chi}$, and $e^{\mp s}$ for a whole transcript
-- statement:
--   Fix a single-challenge adversary with its coins, a threshold $U$ and a common threshold parameter $s > 0$. An endpoint is $e = (k, \mathrm{cross})$ for a first crossing at round $k \le T$, or $e = (T, \text{no-cross})$. At a phase-start history $H$ (including its current aggregate), let $p_b(e \mid H)$ be its probability in world $b$, and let $\chi(H, e) \in \{0,1\}$ indicate that the replay through this endpoint contains the unequal record pair within this phase. Then:
--
--   1. every allowed endpoint has positive (and finite) probability in both worlds, and
--   $$
--   e^{-s\chi(H,e)} \le \frac{p_0(e \mid H)}{p_1(e \mid H)} \le e^{s\chi(H,e)} ; \tag{24}
--   $$
--   2. every complete transcript, with phase histories and endpoints $(H_j, e_j)$, satisfies
--   $$
--   \sum_j \chi(H_j, e_j) \le 1, \qquad e^{-s} \le \prod_j \frac{p_0(e_j \mid H_j)}{p_1(e_j \mid H_j)} \le e^{s} . \tag{25}
--   $$
--   The bounds include phases ending at $T$ and runs reaching the public cap.
--
--   This is the threshold-shift argument of AboveThreshold applied to the counterfactual continuation; it charges the privacy cost of all threshold tests to the single challenge phase.
--
--   **Formalization Note** $p_b(e\mid H)$ is the paper's expression $\int G_b(x) f(x)\,dx$ (`endpointProb`). Ratios are stated multiplicatively in both directions.
--
--   Differences from the source:
--
--   - encoding: p_b(e | H), the probability of the endpoint in world b → endpointProb, the paper's formula ∫ G_b(x) f(x) dx from the proof; reason: this is the paper's own expression for the endpoint probability
--   - encoding: e^{−sχ} ≤ p₀/p₁ ≤ e^{sχ} → p₀ ≤ e^{sχ} p₁ and p₁ ≤ e^{sχ} p₀, with 0 < p_b < ∞; reason: equivalent for positive finite probabilities, and avoids division
--   - generalization: every complete augmented transcript → every phase decomposition of any classifier transcript, complete or not; reason: complete transcripts are phase decompositions
--   - generalization: a structurally valid phase-start history and a threshold U > 0 → every start round t₀ < T, any past classifiers and any aggregate g, and every real U; reason: the threshold-shift proof uses none of these restrictions; valid histories and U > 0 are instances
--   - encoding: endpoints (k, cross), k ≤ T, and (T, no-cross), 1-based rounds → (k, true) with t₀ ≤ k < T and (T, false), 0-based rounds; reason: same endpoints
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.2, (24), (25), p.22

import Mathlib
import Definitions.Def_PrivLittlestone_endpointProb
import Definitions.Def_PrivLittlestone_challengeIndicator
import Definitions.Def_PrivLittlestone_IsPhaseDecomposition
import Definitions.Def_PrivLittlestone_worldInput
import Definitions.Def_PrivLittlestone_IsSingleChallenge

namespace PrivLittlestone

/-- **Lemma B.2 (Endpoint ratios and the challenge phase)** (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Lemma B.2, (24) and (25), p.22). Fix a single-challenge adversary strategy (its coins fixed), a
threshold `U` and a common threshold parameter `s > 0`.
1. (24) At every phase-start history `H` (start round `t₀ < T`, any past classifiers, the phase
   aggregate `g`) and every endpoint `e` (a first crossing `(k, cross)`, `t₀ ≤ k < T`, or
   `(T, no-cross)`), the endpoint probabilities `p_b(e | H)` in the two worlds are positive and
   finite, and `e^{−sχ(H,e)} ≤ p₀(e | H)/p₁(e | H) ≤ e^{sχ(H,e)}`.
2. (25) Every complete transcript with phase histories and endpoints `(H_j, e_j)` satisfies
   `∑_j χ(H_j, e_j) ≤ 1` and `e^{−s} ≤ ∏_j p₀(e_j | H_j)/p₁(e_j | H_j) ≤ e^s`, including phases ending
   at `T` and runs reaching the public cap.

**Formalization Note** The ratio bounds are stated multiplicatively (`p₀ ≤ e^{sχ} p₁` and
`p₁ ≤ e^{sχ} p₀`), which is equivalent given positivity and finiteness. (25) is stated for every
phase decomposition of a transcript, complete or not. -/
theorem lemma_B_2 {X : Type*} {T : ℕ} (adv : Adversary X T) (hadv : IsSingleChallenge adv)
    (s Uth : ℝ) (hs : 0 < s) :
    (∀ (t₀ : ℕ) (past : Fin T → X → Bool) (g : X → Bool) (e : ℕ × Bool), t₀ < T →
      ((e.2 = true ∧ t₀ ≤ e.1 ∧ e.1 < T) ∨ (e.2 = false ∧ e.1 = T)) →
      (∀ b : Bool, 0 < endpointProb (worldInput adv b) past t₀ g s Uth e ∧
        endpointProb (worldInput adv b) past t₀ g s Uth e ≠ ⊤) ∧
      endpointProb (worldInput adv false) past t₀ g s Uth e ≤
        ENNReal.ofReal (Real.exp (s * (challengeIndicator adv past t₀ g e : ℝ))) *
          endpointProb (worldInput adv true) past t₀ g s Uth e ∧
      endpointProb (worldInput adv true) past t₀ g s Uth e ≤
        ENNReal.ofReal (Real.exp (s * (challengeIndicator adv past t₀ g e : ℝ))) *
          endpointProb (worldInput adv false) past t₀ g s Uth e) ∧
    (∀ (gs : Fin T → X → Bool) (ph : List (ℕ × (X → Bool) × (ℕ × Bool))),
      IsPhaseDecomposition gs ph →
      (ph.map fun p => challengeIndicator adv gs p.1 p.2.1 p.2.2).sum ≤ 1 ∧
      (ph.map fun p => endpointProb (worldInput adv false) gs p.1 p.2.1 s Uth p.2.2).prod ≤
        ENNReal.ofReal (Real.exp s) *
          (ph.map fun p => endpointProb (worldInput adv true) gs p.1 p.2.1 s Uth p.2.2).prod ∧
      (ph.map fun p => endpointProb (worldInput adv true) gs p.1 p.2.1 s Uth p.2.2).prod ≤
        ENNReal.ofReal (Real.exp s) *
          (ph.map fun p => endpointProb (worldInput adv false) gs p.1 p.2.1 s Uth p.2.2).prod) := by sorry

end PrivLittlestone
