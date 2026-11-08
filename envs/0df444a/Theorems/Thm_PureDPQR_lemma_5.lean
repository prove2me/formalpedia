-- Prove2me | Theorems.Thm_PureDPQR_lemma_5
-- name    : PureDPQR.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:23.889208+00:00
-- url     : https://prove2.me/theorems/8057e7a2-01fe-4beb-9995-86fb0caa5ec7
-- title:
--   Lemma 5, p.13 — post-processing preserves $(\varepsilon,\delta)$-DP
-- statement:
--   **Lemma 5** (Post-processing). Let $\varepsilon\ge0$, $0\le\delta<1$, and let $M$ be a randomized mechanism on histograms of mass $N$ that is $(\varepsilon,\delta)$-DP (Definition 4). If $g$ uses only the output of $M$, public information and fresh randomness, then $g\circ M$ is $(\varepsilon,\delta)$-DP.
--
--   It passes the privacy of the transcript law to the released synthetic distribution in Proposition 22.
--
--   **Formalization Note** $g$ is a Markov kernel from the output space of $M$ to a measurable space; $g\circ M$ has output law $\int g(o)\,dM(h)(o)$ (`Measure.bind`).
--
--   Differences from the source:
--   - reading: g uses only its output, public information, and fresh randomness → a Markov kernel g from O to O′, and g ◦ M has law (M h).bind g; reason: public information is fixed with g and fresh randomness makes g a kernel; deterministic measurable maps are the special case
--   - encoding: adjacency h′ = h + e_a − e_b on ℕ^d → h′ + e_b = h + e_a; reason: no truncated subtraction; the same pairs
--   - encoding: a mechanism M on H_{N,d} → a family M : (Fin d → ℕ) → Measure O with every M h a probability measure; reason: values off H_{N,d} never enter IsDP, so a mechanism on H_{N,d} extends by any fixed law; a mechanism has probability laws
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Lemma 5, p.13 (PDF p.14); Definition 4, p.13

import Mathlib
import Definitions.Def_PureDPQR_IsDP

open MeasureTheory ProbabilityTheory

namespace PureDPQR

/-- **Lemma 5** (Post-processing [DR14]), p.13 (PDF p.14).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"If M is (ε, δ)-DP and g uses only its output, public information, and fresh randomness, then
g ◦ M is (ε, δ)-DP."

**Formalization Note.** DP is Definition 4 (`IsDP`) for parameters in its range `ε ≥ 0`,
`0 ≤ δ < 1`. A randomized mechanism is the family `M h` of its output laws (probability
measures). A post-processing `g` that uses only the output, public information and fresh
randomness is a Markov kernel from the output space `O` to a measurable space `O'` (public
information is fixed with the kernel; a deterministic measurable `g` is the special case of a
deterministic kernel). `g ◦ M` has output law `(M h).bind g`. -/
theorem lemma_5 {O O' : Type*} [MeasurableSpace O] [MeasurableSpace O'] (N d : ℕ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ < 1) (M : (Fin d → ℕ) → Measure O)
    [∀ h, IsProbabilityMeasure (M h)] (g : Kernel O O') [IsMarkovKernel g]
    (hM : IsDP N d M ε δ) :
    IsDP N d (fun h => (M h).bind g) ε δ := by sorry

end PureDPQR
