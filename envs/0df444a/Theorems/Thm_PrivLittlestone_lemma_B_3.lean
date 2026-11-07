-- Prove2me | Theorems.Thm_PrivLittlestone_lemma_B_3
-- name    : PrivLittlestone.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:35.543634+00:00
-- url     : https://prove2.me/theorems/d0f2ee08-377f-4321-99a6-d6395370fe4c
-- title:
--   Lemma B.3 — composition of sampling and threshold phases is $(\varepsilon_c + s, e^s\delta_c)$-private, and the parameter arithmetic giving $(\varepsilon,\delta)$
-- statement:
--   1. Suppose every candidate-release kernel is $(\varepsilon_s, 3\tau)$-private at common histories, with $\varepsilon_s \le 1$, that there are at most $Km$ candidate releases, and that the threshold kernels satisfy Lemma B.2 with parameter $s > 0$. For any $0 < \delta_0 < 1$, put
--   $$
--   \varepsilon_c = \sqrt{2\log(1/\delta_0) K m \varepsilon_s^2} + 2Km\varepsilon_s^2, \qquad \delta_c = \delta_0 + 3Km\tau .
--   $$
--   Then the complete augmented transcript is $(\varepsilon_c + s, e^s\delta_c)$-private in the adaptive single-challenge model: for every event $E$,
--   $$
--   P_0(E) \le e^{\varepsilon_c + s} P_1(E) + \delta_c, \qquad P_1(E) \le e^{\varepsilon_c + s} P_0(E) + e^{s}\delta_c .
--   $$
--   2. For the parameters (4)–(6), take $s = \varepsilon_a = \varepsilon/2$ and $\delta_0 = \delta/4$. Then, for $K, m, T \ge 1$, $0 < \varepsilon \le 1$, $0 < \delta \le 1/2$: $\varepsilon_s \le 1$,
--   $$
--   Km\varepsilon_s^2 = \frac{\varepsilon^2}{128L_\delta}, \quad \varepsilon_c = \frac{\varepsilon}{8} + \frac{\varepsilon^2}{64L_\delta}, \quad \delta_c = \frac{\delta}{4} + \frac{3\delta}{16(T+1)} \le \frac{11\delta}{32},
--   $$
--   $$
--   \varepsilon_c + s = \frac{5\varepsilon}{8} + \frac{\varepsilon^2}{64L_\delta} < \varepsilon, \qquad e^{s}\delta_c \le \frac{11e^{1/2}}{32}\delta < \delta .
--   $$
--
--   Together with Lemmas B.1 and B.2 this gives the $(\varepsilon, \delta)$-privacy of the continual learner.
--
--   **Formalization Note** In part 1 the augmented transcript is modelled as a sequential interaction whose steps are, at each common history, candidate releases or threshold steps, with world-$b$ kernels $\kappa^b$; Lemma B.2 enters as the hypothesis that along every path the products of the threshold-step probabilities in the two worlds are within a factor $e^{\pm s}$.
--
--   Differences from the source:
--
--   - generalization: the complete augmented transcript of the continual learner → every sequential interaction of candidate-release and threshold kernels satisfying the hypotheses; reason: the augmented transcript of Algorithm 1 at fixed adversary coins is such an interaction
--   - encoding: the threshold kernels satisfy Lemma B.2 with parameter s → the products of threshold-step probabilities along every path are within e^{±s} in both directions; reason: this is (25), the form the proof uses
--   - encoding: privacy in the adaptive single-challenge model → the inequalities for the two transcript laws at fixed adversary coins; reason: averaging over the coins gives the randomized view, as in the paper's proof
--   - generalization: (ε_c + s, e^s δ_c)-privacy in both directions → P₀(E) ≤ e^{ε_c+s} P₁(E) + δ_c and P₁(E) ≤ e^{ε_c+s} P₀(E) + e^s δ_c; reason: the pair of inequalities displayed in the paper's proof; δ_c ≤ e^s δ_c gives the printed form
--   - reading: at most Km candidate releases, stated in the proof and implied by the K phases of m draws → an explicit hypothesis of the abstract interaction, with 0 ≤ ε_s, 0 ≤ τ, 0 < s; reason: an abstract interaction has no phase structure of its own; Algorithm 1 satisfies them
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma B.3, p.23, and the parameter arithmetic, pp.23–24

import Mathlib
import Definitions.Def_PrivLittlestone_seqPMF
import Definitions.Def_PrivLittlestone_epsA
import Definitions.Def_PrivLittlestone_epsS
import Definitions.Def_PrivLittlestone_tauP

namespace PrivLittlestone

open Classical in
/-- **Lemma B.3 (Composition of sampling and threshold phases)**, with the parameter arithmetic
that follows it (He–He, *Private Online Learning of Littlestone Classes and Matroid Flats*, STOC
2027 submission manuscript (sha256 21480556…c562), Lemma B.3, p.23, and pp.23–24).
1. The augmented transcript is a sequential interaction whose steps are, at each common
   history, either candidate releases or threshold (endpoint) steps; world `b` uses the kernels
   `κ_b`. Suppose every candidate-release kernel is `(ε_s, 3τ)`-private at common histories, with
   `ε_s ≤ 1`, along every path there are at most `Km` candidate releases, and the threshold kernels
   satisfy Lemma B.2 with parameter `s`: on every complete transcript the product of the
   threshold-step probabilities in world `0` and in world `1` are within a factor `e^{±s}`. For any
   `0 < δ₀ < 1`, put `ε_c = √(2 log(1/δ₀) K m ε_s²) + 2Kmε_s²` and `δ_c = δ₀ + 3Kmτ`. Then the
   complete augmented transcript is `(ε_c + s, e^s δ_c)`-private:
   `P₀(E) ≤ e^{ε_c+s} P₁(E) + δ_c` and `P₁(E) ≤ e^{ε_c+s} P₀(E) + e^s δ_c` for every event `E`.
2. For the parameters (4)–(6), with `s = ε_a = ε/2` and `δ₀ = δ/4`, and `K, m, T ≥ 1`,
   `0 < ε ≤ 1`, `0 < δ ≤ 1/2`: `ε_s ≤ 1`, `Kmε_s² = ε²/(128 L_δ)`, `ε_c = ε/8 + ε²/(64 L_δ)`,
   `δ_c = δ/4 + 3δ/(16(T + 1)) ≤ 11δ/32`, `ε_c + s = 5ε/8 + ε²/(64 L_δ) < ε` and
   `e^s δ_c ≤ (11e^{1/2}/32) δ < δ`.

**Formalization Note** Part 1 is stated for every such interaction (kernels as probability mass
functions on an arbitrary output type, the step kind `isCand` a function of the common history);
the augmented transcript of Algorithm 1 at fixed adversary coins is an instance. Lemma B.2's
conclusion enters as the hypothesis `hthr`, stated multiplicatively in both directions. -/
theorem lemma_B_3 :
    (∀ {α : Type*} (κ₀ κ₁ : (i : ℕ) → (Fin i → α) → PMF α) (isCand : (i : ℕ) → (Fin i → α) → Prop)
      (n K m : ℕ) (εs τ s δ₀ : ℝ), 0 ≤ εs → εs ≤ 1 → 0 ≤ τ → 0 < s → 0 < δ₀ → δ₀ < 1 →
      (∀ i : ℕ, i < n → ∀ h : Fin i → α, isCand i h → ∀ E : Set α,
        (κ₀ i h).toOuterMeasure E ≤
            ENNReal.ofReal (Real.exp εs) * (κ₁ i h).toOuterMeasure E + ENNReal.ofReal (3 * τ) ∧
          (κ₁ i h).toOuterMeasure E ≤
            ENNReal.ofReal (Real.exp εs) * (κ₀ i h).toOuterMeasure E + ENNReal.ofReal (3 * τ)) →
      (∀ w : Fin n → α,
        (Finset.univ.filter fun i : Fin n => isCand i (fun j => w (Fin.castLE i.isLt.le j))).card
          ≤ K * m) →
      (∀ w : Fin n → α,
        (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ isCand i (fun j => w (Fin.castLE i.isLt.le j))),
            κ₀ i (fun j => w (Fin.castLE i.isLt.le j)) (w i)) ≤
          ENNReal.ofReal (Real.exp s) *
            ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ isCand i (fun j => w (Fin.castLE i.isLt.le j))),
              κ₁ i (fun j => w (Fin.castLE i.isLt.le j)) (w i) ∧
        (∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ isCand i (fun j => w (Fin.castLE i.isLt.le j))),
            κ₁ i (fun j => w (Fin.castLE i.isLt.le j)) (w i)) ≤
          ENNReal.ofReal (Real.exp s) *
            ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ isCand i (fun j => w (Fin.castLE i.isLt.le j))),
              κ₀ i (fun j => w (Fin.castLE i.isLt.le j)) (w i)) →
      ∀ E : Set (Fin n → α),
        (seqPMF κ₀ n).toOuterMeasure E ≤
            ENNReal.ofReal (Real.exp (Real.sqrt (2 * Real.log (1 / δ₀) * K * m * εs ^ 2) +
              2 * K * m * εs ^ 2 + s)) * (seqPMF κ₁ n).toOuterMeasure E +
            ENNReal.ofReal (δ₀ + 3 * K * m * τ) ∧
          (seqPMF κ₁ n).toOuterMeasure E ≤
            ENNReal.ofReal (Real.exp (Real.sqrt (2 * Real.log (1 / δ₀) * K * m * εs ^ 2) +
              2 * K * m * εs ^ 2 + s)) * (seqPMF κ₀ n).toOuterMeasure E +
            ENNReal.ofReal (Real.exp s * (δ₀ + 3 * K * m * τ))) ∧
    (∀ (K m T : ℕ) (ε δ : ℝ), 1 ≤ K → 1 ≤ m → 1 ≤ T → 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
      epsS K m ε δ ≤ 1 ∧
      (K : ℝ) * m * epsS K m ε δ ^ 2 = ε ^ 2 / (128 * Ldelta δ) ∧
      Real.sqrt (2 * Real.log (1 / (δ / 4)) * K * m * epsS K m ε δ ^ 2) +
          2 * K * m * epsS K m ε δ ^ 2 = ε / 8 + ε ^ 2 / (64 * Ldelta δ) ∧
      δ / 4 + 3 * K * m * tauP K m T δ = δ / 4 + 3 * δ / (16 * ((T : ℝ) + 1)) ∧
      δ / 4 + 3 * K * m * tauP K m T δ ≤ 11 * δ / 32 ∧
      ε / 8 + ε ^ 2 / (64 * Ldelta δ) + epsA ε = 5 * ε / 8 + ε ^ 2 / (64 * Ldelta δ) ∧
      5 * ε / 8 + ε ^ 2 / (64 * Ldelta δ) < ε ∧
      Real.exp (epsA ε) * (δ / 4 + 3 * K * m * tauP K m T δ) ≤ 11 * Real.exp (1 / 2) / 32 * δ ∧
      11 * Real.exp (1 / 2) / 32 * δ < δ) := by sorry

end PrivLittlestone
