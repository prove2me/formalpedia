-- Prove2me | Theorems.Thm_PolyEulerFlow_proposition_38
-- name    : PolyEulerFlow.proposition_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:43.987548+00:00
-- url     : https://prove2.me/theorems/6a98cc7e-1d22-4265-8f6c-d3ffc1d10f0b
-- title:
--   Proposition 38 — active length up to a specified horizon
-- statement:
--   With the constants of Lemmas 31 and 35, there are constants $C_1,C_2>0$ such that, for $s\ge s_0$, $0\le\nu\le\varepsilon^2$, every mesh and every disturbance of level $\nu$:
--
--   1. one cycle (started under the hypotheses of Lemma 35) has active length at most $C_1(1+s)$ up to its next section, uniformly in the mesh;
--   2. every trajectory of the compiled field that stays in the box of Lemma 35 has active length at most $C_2(Q+1)$ up to the first grid time at or beyond any horizon $Q\ge0$; in particular, in the polynomial-time case the prefix up to the decision horizon $Q(s)$ has polynomial active length.
--
--   The lengths are those of the actual (perturbed) increments, $\sum_k\|Z_{k+1}-Z_k\|_\infty$.
--
--   Differences from the source:
--   - generalization: every mesh 0 < η ≤ 1 (one constant step) → every variable mesh 0 < η_k ≤ 1 with Σ η_k = ∞; reason: Corollary 39 (p.34) states that every clock, cut and cycle estimate holds on such meshes; every constant step in (0, 1] is one of them
--   - generalization: the prefix up to the decision horizon Q(s) in the polynomial-time case has polynomial active length → every trajectory staying in the fixed box has active length ≤ C₂(Q + 1) up to the first grid time ≥ Q, for every Q ≥ 0; reason: the constructed trajectories stay in that box (Lemma 35, Proposition 37); a polynomial Q(s) gives a polynomial bound
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Proposition 38, p.34 (PDF 36)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsCycleConstants

namespace PolyEulerFlow

/-- **Proposition 38 (Active length up to a specified horizon)**, p.34 (PDF 36). Bournez, One Polynomial Field for Every Euler Step and the Flow
(manuscript, sha256 c4e01b2b…).

With the constants of Lemmas 31 and 35: one cycle of the constructed dynamics has active length `O(1 + s)`, uniformly in the mesh; and the prefix up to
a horizon `Q` has active length `O(Q + 1)`, so polynomial for a polynomial horizon `Q(s)`. Both bounds hold for perturbed trajectories, with the length
defined by their actual increments.

**Formalization Note** A cycle is one started (at index `0`) under the hypotheses of Lemma 35; its active length is the sum of the sup-norm increments up to
its next section. The prefix bound is stated for every trajectory of the compiled field that stays in the fixed box of Lemma 35 (the constructed
trajectories do, by Lemma 35 and Proposition 37), for every horizon `Q ≥ 0`, up to the first grid index at physical time `≥ Q`; with `Q = Q(s)` a
polynomial it gives the printed polynomial bound. -/
theorem proposition_38 :
    ∃ A0 B0 Cdur Cenv Cnext Dclk ε0 : ℝ, IsUniformClock A0 B0 Cdur Cenv Cnext Dclk ε0 ∧
    ∀ (m g : ℕ) (prog : SeparatedAffineProgram m g) (K : ℕ), 256 ≤ K →
      ∃ (A B : ℝ) (s0 : ℕ) (lo hi : CompiledState m g) (Ccyc Clen1 Clen2 : ℝ), 0 < s0 ∧ 0 < Clen1 ∧ 0 < Clen2 ∧
        IsCycleConstants prog K A0 B0 A B s0 lo hi Ccyc ∧
        ∀ s : ℕ, s0 ≤ s →
          let h := scale s
          let ε := h ^ K
          ∀ (ν : ℝ) (η : ℕ → ℝ) (ξ : ℕ → CompiledState m g), 0 ≤ ν → ν ≤ ε ^ 2 →
            IsAdmissibleMesh η → IsPermittedDisturbance ν ξ →
            (∀ (C Cnext : Fin m → ℝ) (Z0 : CompiledState m g), IsCycleStart prog K A0 B0 A ν h C Cnext Z0 →
              ∀ kk : ℕ → ℕ, IsPhaseEntriesUpTo phaseBit (eulerOrbit (compiledField prog K h) Z0 η ξ) 0 4 kk →
                activeLengthOn (eulerOrbit (compiledField prog K h) Z0 η ξ) 0 (kk 4) ≤ Clen1 * (1 + s)) ∧
            (∀ Z0 : CompiledState m g, (∀ k, eulerOrbit (compiledField prog K h) Z0 η ξ k ∈ Set.Icc lo hi) →
              ∀ Q : ℝ, 0 ≤ Q →
                activeLengthOn (eulerOrbit (compiledField prog K h) Z0 η ξ) 0 (firstGrid η Q) ≤ Clen2 * (Q + 1)) := by sorry

end PolyEulerFlow
