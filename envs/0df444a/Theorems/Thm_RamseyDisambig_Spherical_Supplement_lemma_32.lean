-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_32
-- name    : RamseyDisambig.Spherical.Supplement.lemma_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:28:39.733653+00:00
-- url     : https://prove2.me/theorems/9ddc3f01-d615-4ffd-bd51-51047a73415a
-- title:
--   Lemma 32 — Profile Dual Ramsey implies Multi-Profile Dual Ramsey
-- statement:
--   The Profile Dual Ramsey Conjecture (Conjecture 30) implies the Multi-Profile Dual Ramsey Conjecture (Conjecture 27):
--   $$\mathrm{PDR}\ \Longrightarrow\ \mathrm{MPDR}.$$
--   MPDR asserts that for profiles $\alpha^{(1)},\dots,\alpha^{(s)}$ all refined by a profile $\beta$ and for $r$ colors there is $N$ such that any $r$-colorings $c_i$ of the $\alpha^{(i)}$-partitions of $[N]$ admit a single $\beta$-partition $\pi$ of $[N]$ for which, for each $i$, all $\alpha^{(i)}$-partitions coarsening $\pi$ have the same $c_i$-color.
--
--   Together with Lemma 31 this is Corollary 33. Neither conjecture is assumed; the statement is the implication.
--
--   **Formalization Note** Both conjectures are propositions defined in this supplement over the same profile encoding.
--
--   Differences from the source:
--   - reading: r ∈ ℕ colors (and s profiles in Conjecture 27) → positive r (and s ≥ 1); reason: positive-integer reading; the r = 0 and s = 0 instances hold outright (no Fin 0-coloring exists once α-partitions of [N] exist; with s = 0 any β-partition works), so either choice gives an equivalent proposition
--   - encoding: profiles, rigid surjections, α-partitions, copies, coarsening → Profile structure (Fin-indexed positive rationals summing to 1), rigid surjection = surjective with strictly increasing fibre minima (Finset.min in WithTop), α-partition = rigid surjection with fibre sizes |π⁻¹(j)|/N = α_j, coarsening σ = ψ ∘ π for some map ψ; reason: 0-based Fin indices; the same objects as on p. 27
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 32, p. 31 (proof p. 31); Conjecture 27, p. 28; Conjecture 30, p. 30 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 32, p. 31: Profile Dual Ramsey (Conjecture 30) implies Multi-Profile Dual Ramsey (Conjecture 27). -/
theorem lemma_32 : ProfileDualRamsey → MultiProfileDualRamsey := by sorry

end RamseyDisambig.Spherical.Supplement
