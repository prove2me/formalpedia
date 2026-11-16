-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_34
-- name    : RamseyDisambig.Spherical.Supplement.lemma_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:29:09.05391+00:00
-- url     : https://prove2.me/theorems/3a9fb334-c091-4c48-a2b2-aab7da02940e
-- title:
--   Lemma 34 — Multi-Profile Dual Ramsey gives radial 1/(m+1)-near-spanning copies
-- statement:
--   Assume the Multi-Profile Dual Ramsey Conjecture. Then for every $m\in\mathbb N$ there is $n\in\mathbb N$ such that every symmetric coloring $c:Q_n\times Q_n\to\{0,1\}$ admits a map $\varphi:Q_m\to Q_n$ that is a homothety, is $c$-radial, and is $\tfrac1{m+1}$-near-spanning:
--   $$\operatorname{diam}\varphi(Q_m)\ \ge\ \Bigl(1-\frac{1}{m+1}\Bigr)\operatorname{diam}Q_n .$$
--
--   This is the radial Ramsey statement with the specific near-spanning parameter $1/(m+1)$, from which Lemma 35 derives the full conjecture.
--
--   **Formalization Note** The hypothesis is the proposition `MultiProfileDualRamsey`; homothety, near-spanning and radiality are those of the supplement's radial definitions.
--
--   Differences from the source:
--   - generalization: m ∈ ℕ, read as a positive integer → every m : ℕ, including m = 0; reason: for m = 0 the parameter is 1 and the near-spanning condition is diam ≥ 0, so the instance holds with any n; it specializes to the source's m ≥ 1
--   - reading: r ∈ ℕ colors (and s profiles in Conjecture 27) → positive r (and s ≥ 1); reason: positive-integer reading; the r = 0 and s = 0 instances hold outright (no Fin 0-coloring exists once α-partitions of [N] exist; with s = 0 any β-partition works), so either choice gives an equivalent proposition
--   - encoding: Q_n, Hamming distance, diameters, homothety ratio λ > 0, c-radial, symmetric coloring c : Q_n × Q_n → {0,1} → Cube n = Fin n → Bool, cubeDistance, finiteDiameter of the image, a real ratio t > 0, ∃ f : ℝ → Bool with c (ϕ x) (ϕ x') = f (d x x'), c : Cube n → Cube n → Bool; reason: the published cube model; 'depends only on d_X(x, x′)' is the existence of such an f
--   - encoding: profiles, rigid surjections, α-partitions, copies, coarsening → Profile structure (Fin-indexed positive rationals summing to 1), rigid surjection = surjective with strictly increasing fibre minima (Finset.min in WithTop), α-partition = rigid surjection with fibre sizes |π⁻¹(j)|/N = α_j, coarsening σ = ψ ∘ π for some map ψ; reason: 0-based Fin indices; the same objects as on p. 27
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 34, p. 31 (proof pp. 31–32) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey
import Definitions.Def_RamseyDisambig_Spherical_Supplement_RadialRamsey

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 34, p. 31 (proof pp. 31–32): assuming Multi-Profile Dual Ramsey, for every `m` there
is `n` such that every symmetric coloring of `Q_n × Q_n` admits a `c`-radial
`1/(m+1)`-near-spanning homothetic copy of `Q_m`. -/
theorem lemma_34 : MultiProfileDualRamsey →
    ∀ m : ℕ, ∃ n : ℕ, ∀ c : Cube n → Cube n → Bool, IsSymmetricColoring c →
      ∃ ϕ : Cube m → Cube n,
        IsHomothety ϕ ∧ IsNearSpanning (1 / ((m : ℝ) + 1)) ϕ ∧ IsRadial c ϕ := by sorry

end RamseyDisambig.Spherical.Supplement
