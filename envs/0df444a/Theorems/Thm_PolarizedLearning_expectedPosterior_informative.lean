-- Prove2me | Theorems.Thm_PolarizedLearning_expectedPosterior_informative
-- name    : PolarizedLearning.expectedPosterior_informative
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:18:45.212938+00:00
-- url     : https://prove2.me/theorems/74210a4b-9bf9-4141-8480-d836c7f19de4
-- title:
--   Eq. (3), p. 11 — the expected posterior is higher under high quality: $f(\pi,H)>f(\pi,L)$
-- statement:
--   Let the private signal have accuracy $\alpha$ with $1/2<\alpha\le 1$, and let $f(\pi,Q)=\mathbb E[g(\pi,r_t)\mid q=Q]$ be the expected Bayesian posterior (3) of a consumer with prior $\pi$ when the true quality is $Q$. Then for every prior $\pi\in(0,1)$,
--   $$f(\pi,H)>f(\pi,L).$$
--
--   Because the signal is informative, a consumer's updated belief is on average higher when the content is good; this is the monotonicity that drives the drift of the consumption process.
--
--   Differences from the source:
--   - reading: f(π,H) > f(π,L), no domain for π → for π ∈ (0,1); reason: at π = 0 and π = 1 both sides are 0, resp. 1
--   - encoding: α > 0.5, α a probability (eq. (1)) → 1/2 < al ∧ al ≤ 1; reason: α is the probability in (1); no admissible instance changes
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, §3.3, sentence before eq. (3), p. 11 (PDF 11)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

namespace PolarizedLearning

/-- **The expected posterior is higher under high quality**, Kadiyala–Shin, *Social Learning and
Content Quality under Polarization*, MSOM (2024), doi:10.1287/msom.2022.0533, §3.3, sentence
before eq. (3), p. 11 (PDF 11): "Because the private signal `r_t` is informative, … `f(π,H) > f(π,L)`".

For a signal accuracy `1/2 < α ≤ 1` and every prior `π ∈ (0,1)`, `f(π, H) > f(π, L)`.

**Formalization Note.** The page states no domain for `π`; at `π ∈ {0, 1}` the two sides are
equal (both `0`, resp. `1`), so the strict inequality is stated on `(0,1)`. `α ≤ 1` only records
that `α` is a probability in (1); the fact also holds at `α = 1`. -/
theorem expectedPosterior_informative (al : ℝ) (hal_lo : 1 / 2 < al) (hal_hi : al ≤ 1) :
    ∀ π ∈ Set.Ioo (0 : ℝ) 1, f al π .low < f al π .high := by sorry

end PolarizedLearning
