-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_theorem_21
-- name    : RamseyDisambig.Spherical.Supplement.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:30:30.552399+00:00
-- url     : https://prove2.me/theorems/6455e673-aa64-4676-b40e-4da9580750fc
-- title:
--   Theorem 21 — Homogeneous Dual Ramsey implies Near-Spanning Radial Ramsey
-- statement:
--   The Homogeneous Dual Ramsey Conjecture (Conjecture 7) implies the Near-Spanning Radial Ramsey Conjecture (Conjecture 6):
--   $$\mathrm{HDR}\ \Longrightarrow\ \mathrm{NSRR}.$$
--   HDR (Kechris–Sokić–Todorčević) asserts: for $k\mid m$ and every $r$ there is $n$ divisible by $m$ such that every $r$-coloring of the $k$-equipartitions of $[n]$ admits an $m$-equipartition $P$ all of whose $k$-equipartition coarsenings have the same color. NSRR asserts: for all $0<\varepsilon<1/2$ and $m$ there is $N$ such that every symmetric coloring $c:Q_N\times Q_N\to\{0,1\}$ admits a $c$-radial $\varepsilon$-near-spanning homothetic copy of $Q_m$.
--
--   This is the main result of Appendix A: with Lemma 20 it gives a conditional route from homogeneous dual Ramsey theory to the Gap-Hamming Disambiguation theorem. Neither conjecture is assumed or posed; the statement is the implication.
--
--   **Formalization Note** Both conjectures are propositions defined in this supplement (finpartitions for HDR, the published Hamming cube for NSRR).
--
--   Differences from the source:
--   - reading: k, m, r ∈ ℕ in Conjecture 7 → positive k, m, r; reason: positive-integer reading of ℕ recorded for this paper; as a hypothesis the positive form is the weaker assumption, and the zero instances hold outright under this encoding (no k-equipartition of [0] for k ≥ 1, an empty r = 0 coloring exists only when there is nothing to color)
--   - generalization: m ∈ ℕ in Conjecture 6, read as a positive integer → every m : ℕ, including m = 0; reason: the m = 0 instance holds (with N = 0 and ϕ the identity of Q_0), so the stated proposition specializes to the source's
--   - encoding: k-equipartitions of [n], coarsening, r-colorings → Finpartition of Finset.univ : Finset (Fin n) with k equal-size parts, Mathlib's refinement order P ≤ Q, maps into Fin r; reason: [n] is Fin n; Finpartition parts are nonempty; P ≤ Q says every part of P lies in a part of Q, i.e. Q is obtained by merging parts of P
--   - encoding: Q_n, Hamming distance, diameters, homothety ratio λ > 0, c-radial, symmetric coloring c : Q_n × Q_n → {0,1} → Cube n = Fin n → Bool, cubeDistance, finiteDiameter of the image, a real ratio t > 0, ∃ f : ℝ → Bool with c (ϕ x) (ϕ x') = f (d x x'), c : Cube n → Cube n → Bool; reason: the published cube model; 'depends only on d_X(x, x′)' is the existence of such an f
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 21, p. 24 (proof §§A.3–A.5, pp. 27–32) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey
import Definitions.Def_RamseyDisambig_Spherical_Supplement_RadialRamsey

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Theorem 21, p. 24 (proof §§A.3–A.5, pp. 27–32): Homogeneous Dual Ramsey (Conjecture 7) implies Near-Spanning Radial Ramsey (Conjecture 6). An implication; neither conjecture is assumed. -/
theorem theorem_21 : HomogeneousDualRamsey → NearSpanningRadialRamsey := by sorry

end RamseyDisambig.Spherical.Supplement
