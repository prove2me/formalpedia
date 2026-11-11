-- Prove2me | Theorems.Thm_SwapDisk_Main_theorem_D_2
-- name    : SwapDisk.Main.theorem_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:18:18.345253+00:00
-- url     : https://prove2.me/theorems/7865b38e-e38e-4ec7-93b7-88da32252157
-- title:
--   Theorem D.2 — prescribed dictionary budget: $\le N$ fixed points give $R_T\le C_{\mathrm{dict}}(\sqrt{TL_\delta}+T/N^2)$ w.p. $1-\delta$, $\mathbb ER_T\le C_{\mathrm{dict}}(\sqrt T+T/N^2)$
-- statement:
--   Let $C_{\mathrm{dict}}=2^{47}$. For every integer $T\ge2$, integer $N\ge1$ and $\delta\in(0,1)$, an admissible learner using a deterministic ex ante dictionary of at most $N$ physical actions guarantees, against every adversary,
--   $$\mathbb P\Big\{R_T\le C_{\mathrm{dict}}\Big(\sqrt{TL_\delta}+\frac T{N^2}\Big)\Big\}\ge1-\delta,\qquad L_\delta=1+\log(1/\delta).$$
--   A separate confidence-independent learner has expected regret at most $C_{\mathrm{dict}}(\sqrt T+T/N^2)$. The same bounds hold for the full virtual tag sum $R^{\mathrm{tag}}_T$ of these learners (tags $J_t$ in a set of at most $N$ tags attached to the dictionary).
--
--   This is the upper half of the fixed-dictionary tradeoff.
--
--   **Formalization Note.** The dictionary is a tuple $a\in(B^2_2)^N$ (repetitions allowed, so at most $N$ distinct points); the learner records its tag $J_t\in\{1,\dots,N\}$ in its post-round state, read by a measurable $\tau$, and $x_t=a_{J_t}$ almost surely against every adversary.
--
--   Differences from the source:
--   - encoding: the online protocol of Eq. (A.11) with standard Borel private states and the Borel σ-field of the weak topology on P(B²₂) → `Learner`/`Adversary`/`law` of the Protocol definition: Giry σ-field on `ProbabilityMeasure Disk`, rounds indexed from 0, one kernel per `t : ℕ` (those with t ≥ T unused), private states standard Borel types; reason: the Giry and weak-topology Borel σ-fields coincide on the Polish space B²₂; the other changes are index conventions; same learners, adversaries and laws
--   - encoding: E[·] and P{·} under the canonical law → Bochner integrals and measures of events under `law`/`sharpLaw` (`ENNReal.ofReal p ≤ μ {…}` for P{…} ≥ p); reason: the integrands are bounded Borel functions (Proposition A.1); same values
--   - encoding: a deterministic ex ante dictionary of at most N physical actions, with the learner's virtual tags → a constant tuple a : Fin N → Disk and a measurable tag readout τ : L.S → Fin N of the post-round learner state with x_t = a(τ(S^L_t)) a.s. against every adversary; reason: the tags live in the learner's private state (§A.3) and number at most N (Eq. (D.6)); a tuple allows repetitions, i.e. at most N distinct points
--   - encoding: full virtual tag sum → `tagSum a (τ-tags) g` = ∑_j ψ_{a_j}(G_j); reason: Eq. (A.7) for these tags
--   - reading: "the same bounds hold for its full virtual tag sum" (the referent of "its" is ambiguous between the two learners) → the tag-sum bound is stated for both learners, the probability bound for the δ-learner and the expectation bound for the confidence-independent one; reason: the stronger of the two readings, and the one the proof on p. 43 gives (R^tag_T is bounded on the potential event for the δ-learner and E R^tag_T ≤ C_par(γT + 2/γ) for the other)
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 43, Theorem D.2

import Mathlib
import Definitions.Def_SwapDisk_Main_Protocol

open MeasureTheory

namespace SwapDisk.Main

/-- Theorem D.2 (An exact prescribed dictionary budget), p. 43: for `T ≥ 2`, `N ≥ 1`,
`δ ∈ (0, 1)`, a learner with a deterministic dictionary `a ∈ (B²₂)^N` (tags `Fin N`, the tag
`J_t = τ(S^L_t)` read from its post-round state, `x_t = a_{J_t}` a.s.) has, against every
adversary, `P{R_T ≤ C_dict(√(T L_δ) + T/N²)} ≥ 1 − δ`, `L_δ = 1 + log(1/δ)`, `C_dict = 2^47`; a
separate δ-free learner has `E R_T ≤ C_dict(√T + T/N²)`; the same bounds hold for their tag
sums `R^tag_T`. -/
theorem theorem_D_2 (T N : ℕ) (hT : 2 ≤ T) (hN : 1 ≤ N) :
    (∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ (L : Learner) (a : Fin N → Disk) (τ : L.S → Fin N), Measurable τ ∧
        (∀ (D : Adversary) (t : Fin T),
          ∀ᵐ z ∂(law L D T), (Traj.hist z t).2.2 = a (τ (z.2 t).2.1)) ∧
        ∀ D : Adversary,
          ENNReal.ofReal (1 - δ) ≤ law L D T {z | (Traj.hist z).regret ≤
            (2 : ℝ) ^ 47 * (Real.sqrt (T * (1 + Real.log (1 / δ))) + (T : ℝ) / (N : ℝ) ^ 2)} ∧
          ENNReal.ofReal (1 - δ) ≤ law L D T
            {z | tagSum a (fun t => τ (z.2 t).2.1) (Traj.hist z).losses ≤
              (2 : ℝ) ^ 47 * (Real.sqrt (T * (1 + Real.log (1 / δ))) + (T : ℝ) / (N : ℝ) ^ 2)}) ∧
    ∃ (L : Learner) (a : Fin N → Disk) (τ : L.S → Fin N), Measurable τ ∧
      (∀ (D : Adversary) (t : Fin T),
        ∀ᵐ z ∂(law L D T), (Traj.hist z t).2.2 = a (τ (z.2 t).2.1)) ∧
      ∀ D : Adversary,
        expectedRegret T L D ≤ (2 : ℝ) ^ 47 * (Real.sqrt T + (T : ℝ) / (N : ℝ) ^ 2) ∧
        ∫ z, tagSum a (fun t => τ (z.2 t).2.1) (Traj.hist z).losses ∂(law L D T) ≤
          (2 : ℝ) ^ 47 * (Real.sqrt T + (T : ℝ) / (N : ℝ) ^ 2) := by sorry

end SwapDisk.Main
