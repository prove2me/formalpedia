-- Prove2me | Theorems.Thm_PermInvCC_lemma_2_7
-- name    : PermInvCC.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:16.006168+00:00
-- url     : https://prove2.me/theorems/78686378-1747-4b45-aabf-6d1edebbec23
-- title:
--   Lemma 2.7 — $\Phi_n$ is increasing, $\Phi_n(Ds)\le D\Phi_n(s)$, $\Phi_n(s)\ge\max\{s,\log(n+2)\}$
-- statement:
--   Let $n\ge2$ and $\Phi_n(s):=s\log(2+n/s)$ for $s>0$ (logarithms base two). Then
--
--   1. $\Phi_n$ is increasing on $(0,\infty)$;
--   2. $\Phi_n(Ds)\le D\,\Phi_n(s)$ for every $D\ge1$ and $s>0$;
--   3. $\Phi_n(s)\ge\max\{s,\log(n+2)\}$ for every $s\ge1$.
--
--   These elementary bounds control the communication cost in Theorems 3.1 and 1.1.
--
--   Differences from the source:
--   - reading: Φₙ is increasing → StrictMonoOn (Phi n) (Ioi 0); reason: the proof shows Φₙ′ > 0; the strict reading is the stronger one
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 2.7, p.11

import Mathlib
import Definitions.Def_PermInvCC_Phi

namespace PermInvCC

/-- **Lemma 2.7 (A Communication Cost Function)** (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, p.11). Let `Φₙ(s) := s log(2 + n/s)` for `s > 0`. Then `Φₙ` is
increasing, `Φₙ(Ds) ≤ DΦₙ(s)` for `D ≥ 1`, and `Φₙ(s) ≥ max{s, log(n + 2)}` for `s ≥ 1`.

**Formalization Note.** Logarithms are base two (`Real.logb 2`); `n ≥ 2` is the paper's standing
assumption (p.9). "Increasing" is read as strictly increasing on `(0, ∞)` (the proof shows
`Φₙ' > 0`). -/
theorem lemma_2_7 (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (Phi n) (Set.Ioi 0) ∧
    (∀ D s : ℝ, 1 ≤ D → 0 < s → Phi n (D * s) ≤ D * Phi n s) ∧
    (∀ s : ℝ, 1 ≤ s → max s (Real.logb 2 ((n : ℝ) + 2)) ≤ Phi n s) := by sorry

end PermInvCC
