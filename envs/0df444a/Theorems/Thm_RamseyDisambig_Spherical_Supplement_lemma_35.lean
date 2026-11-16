-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_35
-- name    : RamseyDisambig.Spherical.Supplement.lemma_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:29:49.493388+00:00
-- url     : https://prove2.me/theorems/fd151582-9e9c-4604-a08a-214b96e920f9
-- title:
--   Lemma 35 — Multi-Profile Dual Ramsey implies Near-Spanning Radial Ramsey
-- statement:
--   The Multi-Profile Dual Ramsey Conjecture (Conjecture 27) implies the Near-Spanning Radial Ramsey Conjecture (Conjecture 6):
--   $$\mathrm{MPDR}\ \Longrightarrow\ \mathrm{NSRR}.$$
--   NSRR asserts that for all $0<\varepsilon<1/2$ and $m$ there is $N$ such that every symmetric coloring $c:Q_N\times Q_N\to\{0,1\}$ admits a $c$-radial $\varepsilon$-near-spanning homothetic copy of $Q_m$.
--
--   With Corollary 33 (Lemmas 31 and 32) this gives Theorem 21. Neither conjecture is assumed; the statement is the implication.
--
--   **Formalization Note** Both conjectures are propositions defined in this supplement.
--
--   Differences from the source:
--   - generalization: m ∈ ℕ in Conjecture 6, read as a positive integer → every m : ℕ, including m = 0; reason: the m = 0 instance holds (with N = 0 and ϕ the identity of Q_0), so the stated proposition specializes to the source's
--   - reading: r ∈ ℕ colors (and s profiles in Conjecture 27) → positive r (and s ≥ 1); reason: positive-integer reading; the r = 0 and s = 0 instances hold outright (no Fin 0-coloring exists once α-partitions of [N] exist; with s = 0 any β-partition works), so either choice gives an equivalent proposition
--   - encoding: Q_n, Hamming distance, diameters, homothety ratio λ > 0, c-radial, symmetric coloring c : Q_n × Q_n → {0,1} → Cube n = Fin n → Bool, cubeDistance, finiteDiameter of the image, a real ratio t > 0, ∃ f : ℝ → Bool with c (ϕ x) (ϕ x') = f (d x x'), c : Cube n → Cube n → Bool; reason: the published cube model; 'depends only on d_X(x, x′)' is the existence of such an f
--   - encoding: profiles, rigid surjections, α-partitions, copies, coarsening → Profile structure (Fin-indexed positive rationals summing to 1), rigid surjection = surjective with strictly increasing fibre minima (Finset.min in WithTop), α-partition = rigid surjection with fibre sizes |π⁻¹(j)|/N = α_j, coarsening σ = ψ ∘ π for some map ψ; reason: 0-based Fin indices; the same objects as on p. 27
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 35, p. 32 (proof p. 32); Conjecture 6, pp. 6, 24; Conjecture 27, p. 28 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey
import Definitions.Def_RamseyDisambig_Spherical_Supplement_RadialRamsey

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 35, p. 32: Multi-Profile Dual Ramsey (Conjecture 27) implies Near-Spanning Radial Ramsey (Conjecture 6). -/
theorem lemma_35 : MultiProfileDualRamsey → NearSpanningRadialRamsey := by sorry

end RamseyDisambig.Spherical.Supplement
