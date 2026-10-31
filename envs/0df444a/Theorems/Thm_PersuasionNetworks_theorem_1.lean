-- Prove2me | Theorems.Thm_PersuasionNetworks_theorem_1
-- name    : PersuasionNetworks.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:44.414016+00:00
-- url     : https://prove2.me/theorems/4cf45b0e-1324-4900-8a7d-5eaf55bca6cf
-- title:
--   Theorem 1 (corrected: output is consistent and above $b_k$, not always in the band) — Algorithm 1 realizes any feasible solution with C1–C4
-- statement:
--   Let $(p,z)$ be a feasible solution of (OPT) satisfying C1–C4. Then Algorithm 1 has a run with a measurable signal map. For every run and every signal map $f$ of it, the deterministic mechanism $S=f(T)$ satisfies
--   $$
--   \mathbb P(S=k)=p_k,\qquad \mathbb E[T\cdot\mathbf 1\{S=k\}]=z_k\qquad(k=1,\dots,K),
--   $$
--   and, for every $k$ with $p_k>0$,
--   $$
--   \mathbb E[T\mid S=k]=\frac{z_k}{p_k}\ge b_k .
--   $$
--
--   So a feasible solution with C1–C4 is exactly realized by a mechanism in which each signal is sent on at most two intervals of states.
--
--   Differences from the source:
--   - correction: "a level mechanism consistent with (p_k, z_k)" → consistent with (p, z), and E[T | S = k] ≥ b_k; the upper end b_{k−1} is not claimed; reason: (OPT) has no constraint z_k ≤ b_{k−1} p_k: for T uniform on [0, 1], K = 2, b = (1, 1/10, 0), r₁ ≥ r₂, p = (0, 1), z = (0, 1/2) is feasible with C1–C4, and signal 2 has posterior mean 1/2 ∉ [0, 1/10)
--   - generalization: Algorithm 1 constructs a mechanism → a run exists, and the conclusion holds for every run and every measurable signal map; reason: Step S1 says "find"; the printed output is one such run and map
--   - encoding: Algorithm 1 → the relation IsAlgorithm1Run with IsSignalMap, free on the complement of the intervals; reason: that set is μ-null but may be nonempty (the claim [t_m, t_0] ⊃ 𝒯, p.48, can fail) and a mechanism needs a signal at every state
--   - encoding: z_k = E[T·1{S = k}] at p_k = 0 → included in IsConsistent; reason: it is the definition of z_k, p.16, and it equals z_k = 0 of C2
--   - encoding: the end points of the intervals → extended reals, intervals as sets of reals; reason: footnote 24
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Theorem 1, p.19

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism
import Definitions.Def_PersuasionNetworks_Algorithm1

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Theorem 1** (corrected), Candogan, SSRN 3346144 (preprint), p.19 (proof pp.48–51). For a feasible solution `(p, z)` of
(OPT) satisfying C1–C4, Algorithm 1 has a run, with a measurable signal map, and for every run and
every signal map `f` of it the deterministic mechanism `S = f(T)` is consistent with `(p, z)` and has
`E[T | S = k] = z_k / p_k ≥ b_k` when `p_k > 0`.

**Formalization Note.** The page says "a level mechanism consistent with" `(p, z)`. This is false as
printed: (OPT) has no constraint `z_k ≤ b_{k-1} p_k`. Take `T` uniform on `𝒯 = [0, 1]`, `K = 2`,
`b = (1, 1/10, 0)`, `r₁ ≥ r₂`, `p = (0, 1)`, `z = (0, 1/2)`: feasible with C1–C4, and the posterior mean
`1/2` of signal `2` lies outside `[0, 1/10)`. The upper end of the band is therefore not claimed. The
mission's goal `corollary_1` recovers the band for optimal solutions with strictly decreasing `r`. -/
theorem theorem_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (p z : ℕ → ℝ) (hfeas : IsFeasible μ 𝒯 K b p z) (hC : SatisfiesC μ 𝒯 K p z) :
    (∃ (t' t'' : ℕ → EReal) (f : ℝ → ℕ), IsAlgorithm1Run μ 𝒯 K p z t' t'' ∧
      IsSignalMap μ 𝒯 K p z t' t'' f) ∧
    ∀ (t' t'' : ℕ → EReal) (f : ℝ → ℕ), IsAlgorithm1Run μ 𝒯 K p z t' t'' →
      ∀ hf : IsSignalMap μ 𝒯 K p z t' t'' f,
        IsConsistent μ K p z (Kernel.deterministic f hf.measurable) ∧
        ∀ k ∈ Finset.Icc 1 K, 0 < p k → b k ≤ ((z k / p k : ℝ) : EReal) := by sorry

end PersuasionNetworks
