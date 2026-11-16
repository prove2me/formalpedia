-- Prove2me | Theorems.Thm_UnionVolEst_Supplement_theorem_3
-- name    : UnionVolEst.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:09:24.682148+00:00
-- url     : https://prove2.me/theorems/b5145e62-9b3b-4e70-b631-25d70c7dae26
-- title:
--   Theorem 3 — with $\ell_1$-$\theta$-close samplers and $(1\pm\theta)$ volume oracles every algorithm fails with probability $\ge1/2$ on some instance of $O_\varepsilon(1/\theta)$ convex bodies
-- statement:
--   This is the lower bound showing that per-body total-variation guarantees on the samplers do not suffice for union volume estimation.
--
--   Fix $\varepsilon\in(0,1)$. There is a constant $C>0$, depending only on $\varepsilon$, with the following property. For every $\theta\in(0,1)$ there are a dimension $n$ and a number $M$ of bodies with
--   $$
--   1\le M\le C/\theta
--   $$
--   such that every randomized algorithm $A$ fails on some instance. The algorithm may use its own randomness and the oracles below, but it does not see the bodies. The failing instance consists of $M$ convex bodies $K_1,\dots,K_M\subseteq\mathbb R^n$ together with oracles meeting these guarantees:
--
--   1. a sampling oracle for each $K_i$ that returns independent samples from a distribution $D_i$ with $\|D_i-\pi_i\|_1\le\theta$, where $\pi_i$ is the uniform distribution on $K_i$ and $\|\cdot\|_1$ is the $\ell_1$ distance (twice the total variation distance);
--   2. a volume oracle for each $K_i$ returning a value $v_i$ with $(1-\theta)\mathrm{Vol}(K_i)\le v_i\le(1+\theta)\mathrm{Vol}(K_i)$.
--
--   On that instance,
--   $$
--   \Pr\Big[\,A\ \text{returns a value outside}\ \big[(1-\varepsilon)F_0,\,(1+\varepsilon)F_0\big]\Big]\;\ge\;\tfrac12,
--   \qquad F_0=\mathrm{Vol}\Big(\bigcup_{i=1}^M K_i\Big).
--   $$
--
--   The theorem motivates the tail-controlled (almost-$\ell_\infty$) sampler guarantee that Alpona requires instead.
--
--   **Formalization Note** An algorithm is a map of a seed $\omega$, drawn from an arbitrary probability space, the volume answers $v$ and the infinite sample streams $(z_{i,j})_{j\ge0}$. The streams are independent with $z_{i,j}\sim D_i$, and independent of the seed. An adaptive algorithm reads only part of the streams. The algorithm is not assumed measurable: for a non-measurable failure set, the probability is its outer measure. Convex bodies are compact convex sets with nonempty interior. The $\ell_1$ distance is written as twice the published total variation distance `PolySampIso.tvDist`, the supremum of $|D(B)-\pi(B)|$ over measurable $B$.
--
--   Differences from the source:
--   - generalization: any randomized algorithm whose access to the bodies is restricted to the sampling and volume oracles → every map A(ω, v, z) of a seed ω from an arbitrary probability space (Ω, μ), the volume answers v and the infinite sample streams z (z i j the j-th sample of body i, law μ ⊗ ⊗_i ⊗_j D_i); reason: an adaptive oracle algorithm, with any number of queries, reads only part of the streams, so it is such a map; the class is larger, so the statement specializes to the source
--   - generalization: the failure probability of A (A implicitly measurable) → no measurability assumption on A; for a non-measurable failure set the measure is its outer measure; reason: for measurable A this is the failure probability, so it specializes to the source
--   - reading: an instance consisting of K = O_ε(1/θ) convex bodies → ∃ C > 0 depending only on ε such that for every θ ∈ (0, 1) there are n and M with 1 ≤ M ≤ C/θ, chosen before A; reason: the formal content of O_ε(1/θ) uniformly on θ ∈ (0, 1) (the proof's M ≤ (4ε/(1 − ε) + 2)/θ); choosing n and M before A is the stronger order
--   - encoding: a volume oracle returning a (1 ± θ)-approximation to Vol(K_i) → fixed answers v_i with (1 − θ)Vol(K_i) ≤ v_i ≤ (1 + θ)Vol(K_i); reason: the theorem asserts that some valid oracle exists; a deterministic oracle is one (the proof uses one)
--   - encoding: convex bodies K_i, π_i uniform on K_i, ∥·∥₁ the ℓ₁ distance → compact convex sets with nonempty interior in EuclideanSpace ℝ (Fin n); π_i = volume[|K_i]; ∥D_i − π_i∥₁ = 2 · PolySampIso.tvDist D_i π_i, the published TV distance sup over measurable B of |D(B) − π(B)|; reason: standard definitions; the page defines ∥·∥₁ as twice the TV distance
--   - encoding: fails with probability at least 1/2 → the product measure of the set where the output lies outside [(1 − ε)F₀, (1 + ε)F₀] is at least ofReal(1/2); reason: same event; closed interval for (1 ± ε)-approximation
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Theorem 3, §2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_UnionVolEst_IsVolumeApprox
import Definitions.Def_UnionVolEst_unionVolume
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory

universe u

namespace UnionVolEst.Supplement

/-- Theorem 3 (Limitations of approximate sampling) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar,
*Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256
15de4f2e…26bd24), §2.1, printed p.5, PDF p.7): fix `ε ∈ (0, 1)`. There is `C > 0` (depending only
on `ε`) such that for every `θ ∈ (0, 1)` there are a dimension `n` and a number `M ≤ C/θ` of bodies
such that every randomized algorithm `A` that sees only its own randomness, the volume-oracle
answers and the sample streams fails, on some instance of `M` convex bodies in `ℝⁿ` with
oracles meeting the guarantees (`∥D_i − π_i∥₁ ≤ θ`, `(1 ± θ)`-approximate volumes), to return a
`(1 ± ε)`-approximation of the union volume with probability at least `1/2`.

**Formalization Note** "Any randomized algorithm whose access to the input convex bodies is
restricted to the oracles" is a map `A ω v z` of a seed `ω` drawn from an arbitrary probability
space `(Ω, μ)`, the vector `v` of volume answers and the sample streams `z i j` (the `j`-th
sample of body `i`); the streams are independent, `z i j ∼ D_i`, and independent of the seed
(law `μ ⊗ ⊗_i ⊗_j D_i`). An adaptive algorithm reads only part of the streams, so it is such a
map. The volume oracle answers deterministically (the theorem only asserts some valid oracle
exists). `A` need not be measurable: the failure probability is then the outer measure of the
failure set. "`K = O_ε(1/θ)` convex bodies" is `1 ≤ M ≤ C/θ` with `C` chosen before `θ`; `n` and
`M` are chosen before `A`. Convex bodies are compact convex sets with nonempty interior; `π_i`
is the uniform distribution `volume[|K i]`. The ℓ₁ distance "which is twice their TV distance" is
`2 · PolySampIso.tvDist`, the published total variation distance `sup_B |D(B) − π(B)|` over
measurable `B`. -/
theorem theorem_3 (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ n M : ℕ, 1 ≤ M ∧ (M : ℝ) ≤ C / θ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : Ω → (Fin M → ℝ) → (Fin M → ℕ → EuclideanSpace ℝ (Fin n)) → ℝ),
          ∃ K : Fin M → Set (EuclideanSpace ℝ (Fin n)),
            (∀ i, IsCompact (K i) ∧ Convex ℝ (K i) ∧ (interior (K i)).Nonempty) ∧
            ∃ D : Fin M → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
              (∀ i, 2 * PolySampIso.tvDist (D i : Measure (EuclideanSpace ℝ (Fin n))) (volume[|K i]) ≤ θ) ∧
              ∃ v : Fin M → ℝ, (∀ i, IsVolumeApprox θ (K i) (v i)) ∧
                ENNReal.ofReal (1 / 2) ≤
                  (μ.prod (Measure.pi fun i =>
                    Measure.infinitePi fun _ : ℕ => (D i : Measure (EuclideanSpace ℝ (Fin n)))))
                    {p | A p.1 v p.2 ∉
                      Set.Icc ((1 - ε) * unionVolume K) ((1 + ε) * unionVolume K)} := by sorry

end UnionVolEst.Supplement
