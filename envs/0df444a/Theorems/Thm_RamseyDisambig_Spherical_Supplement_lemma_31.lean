-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_31
-- name    : RamseyDisambig.Spherical.Supplement.lemma_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:28:19.399916+00:00
-- url     : https://prove2.me/theorems/6b951448-2343-4ae2-ae26-bb6c919f8b0f
-- title:
--   Lemma 31 — Homogeneous Dual Ramsey implies Profile Dual Ramsey
-- statement:
--   The Homogeneous Dual Ramsey Conjecture (Conjecture 7) implies the Profile Dual Ramsey Conjecture (Conjecture 30):
--   $$\mathrm{HDR}\ \Longrightarrow\ \mathrm{PDR}.$$
--   Here HDR asserts that for $k\mid m$ and $r$ colors some $n$ divisible by $m$ has, for every $r$-coloring of the $k$-equipartitions of $[n]$, an $m$-equipartition all of whose $k$-equipartition coarsenings share a color; PDR asserts the analogue for $\alpha$-partitions and a $\beta$-partition, for profiles $\beta$ refining $\alpha$.
--
--   This is the first step of the proof of Theorem 21. Neither conjecture is assumed; the statement is the implication.
--
--   **Formalization Note** Both conjectures are propositions defined in this supplement; HDR uses Mathlib finpartitions and PDR uses rigid surjections.
--
--   Differences from the source:
--   - reading: k, m, r ∈ ℕ in Conjecture 7 → positive k, m, r; reason: positive-integer reading of ℕ recorded for this paper; as a hypothesis the positive form is the weaker assumption, and the zero instances hold outright under this encoding (no k-equipartition of [0] for k ≥ 1, an empty r = 0 coloring exists only when there is nothing to color)
--   - reading: r ∈ ℕ colors (and s profiles in Conjecture 27) → positive r (and s ≥ 1); reason: positive-integer reading; the r = 0 and s = 0 instances hold outright (no Fin 0-coloring exists once α-partitions of [N] exist; with s = 0 any β-partition works), so either choice gives an equivalent proposition
--   - encoding: k-equipartitions of [n], coarsening, r-colorings → Finpartition of Finset.univ : Finset (Fin n) with k equal-size parts, Mathlib's refinement order P ≤ Q, maps into Fin r; reason: [n] is Fin n; Finpartition parts are nonempty; P ≤ Q says every part of P lies in a part of Q, i.e. Q is obtained by merging parts of P
--   - encoding: profiles, rigid surjections, α-partitions, copies, coarsening → Profile structure (Fin-indexed positive rationals summing to 1), rigid surjection = surjective with strictly increasing fibre minima (Finset.min in WithTop), α-partition = rigid surjection with fibre sizes |π⁻¹(j)|/N = α_j, coarsening σ = ψ ∘ π for some map ψ; reason: 0-based Fin indices; the same objects as on p. 27
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 31, p. 30 (proof p. 30); Conjecture 7, pp. 6, 24; Conjecture 30, p. 30 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 31, p. 30: Homogeneous Dual Ramsey (Conjecture 7) implies Profile Dual Ramsey (Conjecture 30). -/
theorem lemma_31 : HomogeneousDualRamsey → ProfileDualRamsey := by sorry

end RamseyDisambig.Spherical.Supplement
