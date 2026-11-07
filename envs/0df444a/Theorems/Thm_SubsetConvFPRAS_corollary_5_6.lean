-- Prove2me | Theorems.Thm_SubsetConvFPRAS_corollary_5_6
-- name    : SubsetConvFPRAS.corollary_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:01.039781+00:00
-- url     : https://prove2.me/theorems/cdbef144-65ca-41f3-8aa7-9728a907dd65
-- title:
--   Corollary 5.6 — sampling the bases pair law in $O\bigl(\frac{n^2}{t}(n+\log R_\mu R_\nu+n\log\frac{z_{\max}}{z_{\min}}+\min\{a,b\}\log\frac1t+\log\frac1\varepsilon)\bigr)$
-- statement:
--   Assume the standing hypotheses of §5 and take a scalar penalty $0<t\le1$, a field $z\in\mathbb R^U_{>0}$, a pair $(S_0,T_0)\in\operatorname{supp}\pi_{t,z}$, upper bounds $R_\mu,R_\nu$ on the coefficient ranges, and $0<\varepsilon<1$. There is one program of the arithmetic model and one constant $C$ such that on every instance, with
--   $$B=\Bigl\lceil C\,\frac{n^2}{t}\Bigl(n+\log(R_\mu R_\nu)+n\log\frac{z_{\max}}{z_{\min}}+\min\{a,b\}\log\frac1t+\log\frac1\varepsilon\Bigr)\Bigr\rceil,$$
--   every run halts within $B$ steps with a pair in $\operatorname{supp}\pi_{t,z}$, and for every set $A$ of pairs the fraction of $B$-bit tapes whose output lies in $A$ is within $\varepsilon$ of $\pi_{t,z}(A)$; that is, the output is within total variation distance $\varepsilon$ of $\pi_{t,z}$.
--
--   This is the sampler used for every gradient estimate in Corollary 5.12 and every conditional sample in Theorem 5.1.
--
--   **Formalization Note** Input: integer cell $0$ holds $n$; bitmaps $0,1$ hold $S_0,T_0$; real cells $0,1,2,3$ hold $t,R_\mu,R_\nu,\varepsilon$ and cell $4+u$ holds $z_u$. The output pair is left in bitmaps $2,3$. $z_{\max}/z_{\min}$ is the ratio of the largest to the smallest coordinate.
--
--   Differences from the source:
--   - generalization: the coefficient ranges R_μ, R_ν → any upper bounds R_μ, R_ν (RangeLE), with the bound in terms of them; reason: p.4 allows user-supplied upper bounds "with the same replacement in the running-time bounds"; R = the true range is a special case
--   - reading: an unnamed randomness primitive ("chooses with probability p") → fair coins only, one tape bit per coin instruction; reason: the page names no primitive for its arithmetic model; a unit-cost uniform real would be a stronger machine and so a weaker theorem
--   - encoding: an algorithm in the arithmetic model, O(·) operations and oracle calls → one admissible program of the unit-cost real RAM, with the constant C chosen before the instance and work counted per executed instruction; reason: the paper's model (p.44); every instruction costs 1, which only adds to the count
--   - reading: "one can sample … using O(·)" → every run, on every tape, halts within the bound; reason: the proof runs the lazy chain for a fixed number of steps
--   - generalization: a sample within total variation ε → also: the output is in supp π_{t,z} on every tape; reason: Lemma 3.1 requires samplers with supported outputs, and the chain never leaves the support; the source's claim follows by dropping the clause
--   - encoding: total variation distance ≤ ε → |P(output ∈ A) − π(A)| ≤ ε for every set A of pairs; reason: equivalent definition of total variation
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Corollary 5.6, p.21 (proof p.22)

import Mathlib
import Definitions.Def_SubsetConvFPRAS_PairLaws
import Definitions.Def_SubsetConvFPRAS_Machine

open scoped Classical

namespace SubsetConvFPRAS

/-- Chen, Liu, arXiv:2610.06724 (sha256 6c1d68c2…), Corollary 5.6, p.21. One program samples within total
variation distance `ε` of `π_{t,z}`, for scalar `t`, within
`O((n²/t)(n + log(R_μ R_ν) + n log(z_max/z_min) + min{a,b} log(1/t) + log(1/ε)))` operations and oracle calls.

**Formalization Note.** `R_μ, R_ν` may be upper bounds (p.4). The input layout is `initSampler`, and the output
pair is left in bitmaps `2, 3`. The bound holds on every tape, and the output is supported on every tape
(Lemma 3.1 requires a sampler with supported outputs). Total variation is stated event by event: for every
set `A` of pairs, the fraction of tapes with output in `A` is within `ε` of `π_{t,z}(A)`. -/
theorem corollary_5_6 :
    ∃ (P : Program) (C : ℕ), Admissible P ∧
      ∀ (n a b : ℕ) (μ ν : Finset (Fin n) → ℝ), IsHomogeneousPair a b μ ν →
      ∀ (t : ℝ) (z : Fin n → ℝ) (S₀ T₀ : Finset (Fin n)) (Rμ Rν ε : ℝ),
        0 < t → t ≤ 1 → (∀ u, 0 < z u) → 0 < softLaw μ ν (fun _ => t) z (S₀, T₀) →
        RangeLE μ Rμ → RangeLE ν Rν → 0 < ε → ε < 1 →
        let B : ℕ := ⌈(C : ℝ) * ((n : ℝ) ^ 2 / t) *
          ((n : ℝ) + Real.log (Rμ * Rν) + (n : ℝ) * Real.log ((⨆ u, z u) / ⨅ u, z u) +
            (min a b : ℕ) * Real.log (1 / t) + Real.log (1 / ε))⌉₊
        let s₀ := initSampler S₀ T₀ t Rμ Rν ε z
        (∀ ω : ℕ → Bool,
          (run P μ ν s₀ ω B).output.isSome ∧ (run P μ ν s₀ ω B).work ≤ B ∧
            0 < softLaw μ ν (fun _ => t) z ((run P μ ν s₀ ω B).bitmap 2, (run P μ ν s₀ ω B).bitmap 3)) ∧
        ∀ A : Set (Finset (Fin n) × Finset (Fin n)),
          |(tapeCount P μ ν s₀ B (fun st => (st.bitmap 2, st.bitmap 3) ∈ A) : ℝ) / 2 ^ B -
              ∑ x, if x ∈ A then softLaw μ ν (fun _ => t) z x else 0| ≤ ε := by sorry

end SubsetConvFPRAS
